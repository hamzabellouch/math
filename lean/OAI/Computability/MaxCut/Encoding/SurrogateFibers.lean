import Mathlib
import OAI.Computability.MaxCut.Encoding.DimensionSelection
import OAI.Computability.MaxCut.Encoding.PositiveMultiplier
import OAI.Computability.MaxCut.Games.SplitMaps

namespace OAI

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

namespace MaxCutGames.Decoder.SurrogateFibers

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier
open PositiveMultiplier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

/-- Uniform shortcode sampling; neither nonzero-factor conditioning nor
rank-one-matrix-uniform sampling is substituted for its two independent factors. -/
def shortcodeAcceptance (f : (E →ₗ[F2] K) → C) : ℝ := by
  classical
  exact 𝔼 M, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
    if f M = f (M + l.smulRight a) then (1 : ℝ) else 0

omit [Fintype K] [Fintype W] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)] [Fintype (E →ₗ[F2] K × W)] in
theorem product_perturbation (M : E →ₗ[F2] K) (T : E →ₗ[F2] W)
    (l : E →ₗ[F2] F2) (a : K) :
    M.prod T + l.smulRight ((LinearMap.inl F2 K W) a) =
      (M + l.smulRight a).prod T := by
  ext x <;> simp

theorem surrogate_acceptance_eq_fiber_average
    (label : (E →ₗ[F2] K × W) → C) :
    equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 T : E →ₗ[F2] W,
        shortcodeAcceptance (fun M : E →ₗ[F2] K => label (M.prod T)) := by
  classical
  have hsampling : equalityAcceptance (subspaceLaw (LinearMap.inl F2 K W)) label =
      𝔼 X : E →ₗ[F2] K × W, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight ((LinearMap.inl F2 K W) a)) then
          (1 : ℝ) else 0 := by
    unfold equalityAcceptance
    apply Finset.expect_congr rfl
    intro X _
    rw [subspaceLaw_sum, Fintype.expect_eq_sum_div_card]
    ring
  rw [hsampling, SplitMaps.expect_codomain_product, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro T _
  unfold shortcodeAcceptance
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro l _
  rw [product_perturbation]

end
end MaxCutGames.Decoder.SurrogateFibers

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Reduction.ActualSource
open MaxCutGames.Fourier.MatrixNoise

namespace MaxCutGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

theorem expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product Finset.univ Finset.univ f)

theorem expect_eq_uniform_sum {I : Type*} [Fintype I] (f : I → ℝ) :
    (𝔼 i, f i) = ∑ i, (Fintype.card I : ℝ)⁻¹ * f i := by
  rw [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
  ring

/-- The finite noise law's multiplier is exactly the rational kernel event
of the same gadget, cast to the real numbers. -/
theorem eigenvalue_eq_kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P] (S : Ambient s d →ₗ[F2] P) :
    linearNoiseEigenvalue (samplerLaw g.noise) S =
      (Integration.SplitGadget.kernelProbability g S : ℝ) := by
  rw [← sample_kernel_eq_eigenvalue]
  unfold Integration.SplitGadget.kernelProbability
  rw [rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]

/-- The four independent samples of the actual single-orbit test. -/
theorem acceptance_nested (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    (acceptanceProbability S k g label : ℝ) =
      𝔼 U : Question S k, 𝔼 X : Map k s d, 𝔼 i : g.NoiseIndex, 𝔼 l : Dual k,
        if unfolded S k s d label (U, X) =
          unfolded S k s d label (U, X + l.smulRight (g.noise i))
        then (1 : ℝ) else 0 := by
  rw [acceptanceProbability_eq_test, rat_expect_cast]
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero]
  simp only [expect_prod, leftQuery, rightQuery, ActualGame.leftQuery, ActualGame.rightQuery]
  apply Finset.expect_congr rfl
  intro U _
  apply Finset.expect_congr rfl
  intro X _
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro l _
  by_cases h : unfolded S k s d label (U, X) =
      unfolded S k s d label (U, X + l.smulRight (g.noise i)) <;> simp [h]

/-- No auxiliary side labeling is introduced: the same restored table occurs
on both sides of the actual equality test. -/
theorem acceptance_eq_equality_mean (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    (acceptanceProbability S k g label : ℝ) =
      𝔼 U : Question S k,
        equalityAcceptance (samplerLaw g.noise) (fun X : Map k s d =>
          unfolded S k s d label (U, X)) := by
  rw [acceptance_nested]
  apply Finset.expect_congr rfl
  intro U _
  unfold equalityAcceptance
  apply Finset.expect_congr rfl
  intro X _
  rw [← sample_expect_eq]
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro l _
  split_ifs <;> rfl

def fiberAcceptance (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) : ℝ :=
  shortcodeAcceptance (fun M : ActualHomogeneous.E k →ₗ[F2] Alphabet s =>
    unfolded S k s d label (U, M.prod T))

theorem fiberAcceptance_le_one (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) :
    fiberAcceptance S k s d label U T ≤ 1 := by
  unfold fiberAcceptance shortcodeAcceptance
  apply Finset.expect_le Finset.univ_nonempty
  intro M _
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  apply Finset.expect_le Finset.univ_nonempty
  intro l _
  split_ifs <;> norm_num

theorem weighted_fiber_mean_lower (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (μ : Question S k → ℝ) (r : Nat)
    (hμ : ∀ U, 0 ≤ μ U) (hμsum : ∑ U, μ U = 1)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ ∑ U, μ U *
      equalityAcceptance (samplerLaw g.noise)
        (fun X : Map k s d => unfolded S k s d label (U, X))) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      ∑ U, μ U * (𝔼 T, fiberAcceptance S k s d label U T) := by
  have h := matrix_spectral_comparison μ (samplerLaw g.noise) (alphabetEmbedding s d)
    (fun U (X : Map k s d) => unfolded S k s d label (U, X)) r
    hμ hμsum (samplerLaw_nonneg g.noise) (samplerLaw_normalized g.noise)
    (fun L hL => by
      rw [eigenvalue_eq_kernelProbability]
      have hc := (Rat.cast_le (K := ℝ)).mpr (hkernel L hL)
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hc) haccept
  simpa only [alphabetEmbedding, surrogate_acceptance_eq_fiber_average,
    fiberAcceptance] using h

theorem actual_fiber_mean_lower (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) (r : Nat)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℚ) / 100 ≤ acceptanceProbability S k g label) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      𝔼 U : Question S k, 𝔼 T, fiberAcceptance S k s d label U T := by
  rw [expect_eq_uniform_sum]
  apply weighted_fiber_mean_lower S k g label
    (fun _ => (Fintype.card (Question S k) : ℝ)⁻¹) r
  · intro U
    positivity
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply mul_inv_cancel₀
    exact_mod_cast Fintype.card_ne_zero (α := Question S k)
  · exact hkernel
  · have hc := (Rat.cast_le (K := ℝ)).mpr haccept
    rw [acceptance_eq_equality_mean, expect_eq_uniform_sum] at hc
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

def eta (r : Nat) : ℝ := ((2 : ℝ) ^ r)⁻¹ / 16

theorem eta_pos (r : Nat) : 0 < eta r := by unfold eta; positivity

/-- At least `10 η` of the actual `(U,T)` pairs have shortcode acceptance
at least `4 η`, exactly the input needed by row erasure. -/
theorem actual_good_fiber_mass (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) (r : Nat)
    (hkernel : ∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
      r ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
      Integration.SplitGadget.kernelProbability g L ≤ 7 / 8)
    (haccept : (99 : ℚ) / 100 ≤ acceptanceProbability S k g label) :
    10 * eta r ≤ 𝔼 U : Question S k,
      𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
        if 4 * eta r ≤ fiberAcceptance S k s d label U T then (1 : ℝ) else 0 := by
  let I := Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)
  let μ : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹
  let p : I → ℝ := fun a => fiberAcceptance S k s d label a.1 a.2
  have hmean := actual_fiber_mean_lower S k g label r hkernel haccept
  have hmean' : (72 : ℝ) / 5 * eta r ≤ ∑ a, μ a * p a := by
    rw [← expect_eq_uniform_sum, expect_prod]

    unfold eta
    nlinarith
  have h := good_fiber_mass μ p (eta r) (fun _ => by positivity)
    (by simp [μ, Fintype.card_ne_zero]) (eta_pos r).le
    (fun a => fiberAcceptance_le_one S k s d label a.1 a.2) hmean'
  change 10 * eta r ≤
    ∑ a : Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d),
      (Fintype.card (Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)) : ℝ)⁻¹ *
        (if 4 * eta r ≤ fiberAcceptance S k s d label a.1 a.2 then 1 else 0) at h
  rw [← expect_eq_uniform_sum, expect_prod] at h
  exact h

end MaxCutGames.Decoder.ActualSpectral
end

end OAI
