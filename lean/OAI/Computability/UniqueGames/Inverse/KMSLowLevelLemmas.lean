import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.ModularLattice
import OAI.Computability.UniqueGames.Decoding.AdviceFibersLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticBlockFrequenciesLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticCharacterInduction
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyTransportSmallMixed
import OAI.Computability.UniqueGames.Inverse.KMSBasisComparisonPseudorandomTupleMapLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedBaseLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedScalarLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentZoomInAlgebraLemmas

namespace OAI

section

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise
open UniqueGamesTheorem.Decoder.PositiveMultiplier
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

def rankEnergy (rank : I → ℕ) (a : I → ℝ) (i : ℕ) : ℝ :=
  ∑ s, if rank s = i then a s ^ 2 else 0

theorem sum_rankEnergy (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) =
      ∑ s, if rank s ≤ r then a s ^ 2 else 0 := by
  unfold rankEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rank s ≤ r
  · simp [eq_comm, Finset.mem_range, hs]
  · simp [eq_comm, Finset.mem_range, hs]

/-- Exact rank multiplier cutoff, without dimension-dependent constants. -/
theorem spectral_cutoff (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) +
        ((2 : ℝ) ^ (r + 1))⁻¹ * ∑ s, a s ^ 2 := by
  rw [sum_rankEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have ht : 0 ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * a s ^ 2 := by positivity
  by_cases hs : rank s ≤ r
  · rw [ite_eq_left hs]
    have hinv : ((2 : ℝ) ^ rank s)⁻¹ ≤ 1 := by
      rw [← one_div]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hm := mul_le_mul_of_nonneg_right hinv (sq_nonneg (a s))
    nlinarith
  · rw [ite_eq_right hs, zero_add]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg (a s))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem spectral_cutoff_of_level_bounds (rank : I → ℕ) (a : I → ℝ)
    (r : ℕ) (C δ : ℝ) (htotal : (∑ s, a s ^ 2) = δ)
    (hlevels : ∀ i ≤ r, rankEnergy rank a i ≤ C * δ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      ((r + 1 : ℕ) * C + ((2 : ℝ) ^ (r + 1))⁻¹) * δ := by
  have hsum : (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) ≤
      (r + 1 : ℕ) * C * δ := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), C * δ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlevels i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = _ := by simp; ring
  have hcut := spectral_cutoff rank a r
  rw [htotal] at hcut
  nlinarith only [hcut, hsum]
end FiniteCutoff

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual operator samples both rank-one factors uniformly, including zero. -/
def uniformNoise (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  linearRealNoiseOperator (subspaceLaw (LinearMap.id : F →ₗ[F2] F)) f

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniformNoise_apply (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    uniformNoise f X = 𝔼 v : F, 𝔼 l : E →ₗ[F2] F2, f (X + l.smulRight v) := by
  unfold uniformNoise linearRealNoiseOperator
  rw [subspaceLaw_sum]
  simp only [LinearMap.id_apply, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  ring

theorem uniformNoise_energy (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * uniformNoise f X) =
      ∑ S : F →ₗ[F2] E, ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ *
        linearCoeff f S ^ 2 := by
  unfold uniformNoise
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [subspaceLaw_eigenvalue, LinearMap.comp_id]

omit [Fintype F] [Fintype (E →ₗ[F2] F2)] in
theorem rankEnergy_eq (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    rankEnergy (fun S : F →ₗ[F2] E => Module.finrank F2 S.range)
      (linearCoeff f) i = 𝔼 X, rankComponent i f X ^ 2 := by
  rw [rankComponent_energy, Finset.sum_filter]
  rfl

omit [Fintype F] [Fintype (E →ₗ[F2] F2)] in
/-- The scalar fourth-moment argument applied to genuine rank projections. -/
theorem rankComponent_bound (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (r i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hupper : (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (25 * r ^ 3) * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, rankComponent i f X ^ 2) ≤
      (2 : ℝ) ^ (7 * r ^ 3 + 3) * ε ^ ((1 : ℝ) / 4) * (𝔼 X, f X) := by
  apply lowLevel_bound_of_fourthMoment hf (rankComponent i f) r ε hε _ hupper
  exact (component_inner_self _ f).symm

/-- The KMS spectral conclusion once the actual pseudorandom upper fourth
moments have been proved. The error, cutoff and constants precede dimensions. -/
theorem uniformNoise_bound_of_fourthMoments (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBoolean f) (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hupper : ∀ i ≤ r, (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (25 * r ^ 3) * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, f X * uniformNoise f X) ≤
      ((r + 1 : ℕ) * ((2 : ℝ) ^ (7 * r ^ 3 + 3) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹) * (𝔼 X, f X) := by
  rw [uniformNoise_energy]
  apply spectral_cutoff_of_level_bounds
  · rw [linear_parseval, boolean_squared_average hf]
  · intro i hi
    rw [rankEnergy_eq]
    exact rankComponent_bound f hf r i ε hε (hupper i hi)
end ActualFourier

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

section

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open KMSMomentScalar KMSAnalytic
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

/-- No particular polynomial in the cutoff is required for the scalar step. -/
theorem projection_bound_of_general_fourthMoment {X : Type*} [Fintype X]
    {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x)
    (hupper : (𝔼 x, g x ^ 4) ≤ C * (𝔼 x, g x ^ 2) * ε) :
    (𝔼 x, g x ^ 2) ≤ (C + 1) * ε ^ ((1 : ℝ) / 4) * (𝔼 x, f x) := by
  let η : ℝ := 𝔼 x, g x ^ 2
  let δ : ℝ := 𝔼 x, f x
  have hη : 0 ≤ η := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ : 0 ≤ δ := boolean_average_nonneg hf
  have hlow := projection_fifth_le_density_fourth_moment hf g hprojection
  change η ^ 5 ≤ δ ^ 4 * (𝔼 x, g x ^ 4) at hlow
  have hupper' := mul_le_mul_of_nonneg_left hupper (pow_nonneg hδ 4)
  have hsmall : η ^ 4 ≤ C * ε * δ ^ 4 := by
    by_cases hz : η = 0
    · simpa only [hz, zero_pow (by decide : (4 : ℕ) ≠ 0)] using
        mul_nonneg (mul_nonneg hC hε) (pow_nonneg hδ 4)
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hηpos).mp
      nlinarith only [hlow, hupper']
  have hconstant : C ≤ (C + 1) ^ 4 := by
    nlinarith [sq_nonneg C, pow_nonneg hC 3, pow_nonneg hC 4]
  apply le_of_fourth_power_le hη (by positivity)
  calc
    η ^ 4 ≤ C * ε * δ ^ 4 := hsmall
    _ ≤ (C + 1) ^ 4 * ε * δ ^ 4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hε) (pow_nonneg hδ 4)
    _ = _ := by rw [mul_pow, mul_pow, fourth_root_power hε]

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual full-uniform rank-one correlation, with a general moment constant. -/
theorem uniformNoise_bound_of_general_fourthMoments
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (r : ℕ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hupper : ∀ i ≤ r, (𝔼 X, rankComponent i f X ^ 4) ≤
      C * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, f X * uniformNoise f X) ≤
      ((r + 1 : ℕ) * ((C + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹) * (𝔼 X, f X) := by
  rw [uniformNoise_energy]
  apply spectral_cutoff_of_level_bounds
  · rw [linear_parseval, boolean_squared_average hf]
  · intro i hi
    rw [rankEnergy_eq]
    apply projection_bound_of_general_fourthMoment hf (rankComponent i f)
      C ε hC hε _ (hupper i hi)
    exact (component_inner_self _ f).symm
end ActualFourier

/-- Even an arbitrarily large constant depending on r alone permits the
cutoff and tolerance to be chosen before both dimensions. -/
theorem exists_general_cutoff_parameters (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹ ≤ ζ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ζ / 4 by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  let r := max 1 N
  let D : ℝ := C r + 1
  let t : ℝ := min 1 (ζ / (4 * (r + 1 : ℕ) * D))
  let ε : ℝ := t ^ 4
  have hD : 0 < D := by dsimp [D]; linarith [hC r]
  have hr : 1 ≤ r := le_max_left _ _
  have hden : 0 < 4 * (r + 1 : ℕ) * D := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hζ hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hε : 0 < ε := pow_pos ht _
  have hε1 : ε ≤ 1 := pow_le_one₀ ht.le ht1
  have hroot : ε ^ ((1 : ℝ) / 4) = t := by
    have hpow : (ε ^ ((1 : ℝ) / 4)) ^ 4 = t ^ 4 := fourth_root_power hε.le
    have hn : 0 ≤ ε ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hε.le _
    exact le_antisymm (le_of_fourth_power_le hn ht.le hpow.le)
      (le_of_fourth_power_le ht.le hn hpow.symm.le)
  have hlow : (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) ≤ ζ / 4 := by
    rw [hroot]
    have ht' : t ≤ ζ / (4 * (r + 1 : ℕ) * D) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp ht'
    nlinarith only [hm]
  have htail : ((2 : ℝ) ^ (r + 1))⁻¹ < ζ / 4 := by
    have hmon : (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (le_trans (le_max_right 1 N) (Nat.le_succ r))
    simpa only [one_div, inv_pow] using hmon.trans_lt hN
  refine ⟨r, hr, ε, hε, hε1, ?_⟩
  change (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) + _ ≤ ζ / 2
  linarith

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

section

namespace UniqueGamesTheorem.Inverse.KMSMomentToExpansion
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSMomentScalar KMSAnalytic KMSLowLevel

/-- Any proved dimension-independent upper moment with a finite local budget
supplies the exact ordered-basis expansion interface. This lemma is conditional
until the genuine KMS small-component induction supplies `hupper`. -/
theorem liftExpansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    LiftExpansionPrinciple := by
  intro ζ hζ _hζ1
  obtain ⟨r, _hr, ε, hε, hε1, hcut⟩ := exists_general_cutoff_parameters C hC hζ
  refine ⟨ε, hε, hε1, R r, ellMin r, ?_⟩
  intro ell hell
  refine ⟨0, ?_⟩
  intro n _hn S hS hPseudo
  have hf : IsBoolean (liftedIndicator S) := by
    intro X
    unfold liftedIndicator
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 ≤ liftDensity S := boolean_average_nonneg hf
  have hc := uniformNoise_bound_of_general_fourthMoments (liftedIndicator S) hf
    r (C r) ε (hC r) hε.le (hupper r ε hε.le hε1 ell hell n S hPseudo)
  have heq : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) =
      𝔼 X : BasisMap n ell, liftedIndicator S X * uniformNoise (liftedIndicator S) X := by
    apply Finset.expect_congr rfl
    intro X _
    congr 1
    rw [fullStepRetention_eq_noise, uniformNoise_apply]
  apply liftRetention_le_of_correlation_le S hS ζ
  rw [heq]
  apply hc.trans
  change ((r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
    ((2 : ℝ) ^ (r + 1))⁻¹) * liftDensity S ≤ ζ * liftDensity S
  apply mul_le_mul_of_nonneg_right _ hδ
  exact hcut.trans (by linarith)

/-- Checked finite bridges and parameter choices reduce the full KMS expansion
principle to the displayed actual upper-moment estimate, and nothing weaker. -/
theorem expansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    KMS.ExpansionPrinciple :=
  expansion_of_liftExpansion (liftExpansion_of_upperMoments C hC R ellMin hupper)

end
end UniqueGamesTheorem.Inverse.KMSMomentToExpansion

end

section

/-!
Coordinates adapted to an injected distinguished point. The complementary
subspace contains all old injected directions, so that the original injection
becomes exactly `pointLift` in the constructed coordinates.
-/

namespace UniqueGamesTheorem.Inverse.KMSPointComplement

noncomputable section
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open KMSAnalytic (pointLift)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

/-- The coordinates supplied by a complement to a nonzero point. -/
def pointEquivOfIsCompl (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) : (U × F2) ≃ₗ[F2] E :=
  ((LinearEquiv.refl F2 U).prodCongr
    (LinearEquiv.toSpanNonzeroSingleton F2 E v hv)).trans
      (Submodule.prodEquivOfIsCompl U (Submodule.span F2 {v}) hc)

@[simp] theorem pointEquivOfIsCompl_apply (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) (x : U) (c : F2) :
    pointEquivOfIsCompl U v hv hc (x, c) = (x : E) + c • v := rfl

/-- Every injection with a distinguished last coordinate can be expressed
as `pointLift` after a change of coordinates on its target. -/
theorem exists_aligned_point_equiv (ι : (I × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) :
    ∃ U : Submodule F2 E, ∃ e : (U × F2) ≃ₗ[F2] E,
      ∃ κ : I →ₗ[F2] U, Function.Injective κ ∧
        e.toLinearMap.comp (pointLift κ) = ι := by
  let z : I →ₗ[F2] E := ι.comp (LinearMap.inl F2 I F2)
  let v : E := ι (0, 1)
  have hv : v ∉ z.range := by
    rintro ⟨x, hx⟩
    have hx' : ι (x, 0) = ι (0, 1) := hx
    have h01 : (0 : F2) = 1 := congrArg Prod.snd (hι hx')
    exact zero_ne_one h01
  have hv0 : v ≠ 0 := by
    intro h
    apply hv
    rw [h]
    exact z.range.zero_mem
  obtain ⟨U, hU, hc⟩ := (Submodule.disjoint_span_singleton_of_notMem hv).exists_isCompl
  let κ : I →ₗ[F2] U := z.codRestrict U (fun x => hU ⟨x, rfl⟩)
  let e : (U × F2) ≃ₗ[F2] E := pointEquivOfIsCompl U v hv0 hc
  refine ⟨U, e, κ, ?_, ?_⟩
  · intro x y h
    have hxy : ι (x, 0) = ι (y, 0) := congrArg Subtype.val h
    exact congrArg Prod.fst (hι hxy)
  · apply LinearMap.ext
    rintro ⟨x, c⟩
    change ι (x, 0) + c • ι (0, 1) = ι (x, c)
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp

/-- A positive-dimensional binary space admits a last-point coordinate, with
an actual subspace for the remaining coordinates and the exact dimension drop. -/
theorem exists_point_equiv [FiniteDimensional F2 E]
    (h : 0 < Module.finrank F2 E) :
    ∃ U : Submodule F2 E, ∃ _ : (U × F2) ≃ₗ[F2] E,
      Module.finrank F2 U + 1 = Module.finrank F2 E := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  obtain ⟨U, hc⟩ := (Submodule.span F2 {v}).exists_isCompl
  let e := pointEquivOfIsCompl U v hv hc.symm
  refine ⟨U, e, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using e.finrank_eq

end
end UniqueGamesTheorem.Inverse.KMSPointComplement

end

section

/-!
Exact coordinate alignment for the mixed-norm induction. A chosen fixed point
is moved to the last small coordinate, and an actual ambient complement makes
its injection a pointLift. Small-component transport identifies the resulting
functions exactly, so the next recursive estimate concerns the same law.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E E0 F A A0 I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E0] [Module F2 E0]
  [AddCommGroup F] [Module F2 F] [AddCommGroup A] [Module F2 A]
  [AddCommGroup A0] [Module F2 A0] [AddCommGroup I] [Module F2 I]

/-- The injection can be aligned with the fixed-point shuffle on its domain. -/
theorem exists_mixed_aligned_point (ι : (A × I) →ₗ[F2] E)
    (hι : Function.Injective ι) (eA : (A0 × F2) ≃ₗ[F2] A) :
    ∃ U : Submodule F2 E, ∃ eE : (U × F2) ≃ₗ[F2] E,
      ∃ κ : (A0 × I) →ₗ[F2] U, Function.Injective κ ∧
        eE.toLinearMap.comp (pointLift κ) =
          ι.comp (pointShuffle eA).toLinearMap :=
  KMSPointComplement.exists_aligned_point_equiv
    (ι.comp (pointShuffle eA).toLinearMap) (hι.comp (pointShuffle eA).injective)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 E0]
  [FiniteDimensional F2 F] [FiniteDimensional F2 A]
  [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E0 × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (((A0 × I) × F2) →ₗ[F2] F)]
  [Fintype (F →ₗ[F2] ((A0 × I) × F2))]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E0]
  [FiniteDimensional F2 F] [FiniteDimensional F2 A]
  [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (((A0 × I) × F2) →ₗ[F2] F)] in
/-- Exact small function after both coordinate changes. -/
theorem smallComponent_mixed_aligned (ι : (A × I) →ₗ[F2] E)
    (eA : (A0 × F2) ≃ₗ[F2] A) (eE : (E0 × F2) ≃ₗ[F2] E)
    (κ : (A0 × I) →ₗ[F2] E0)
    (halign : eE.toLinearMap.comp (pointLift κ) =
      ι.comp (pointShuffle eA).toLinearMap) (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent (pointLift κ)
      (fun X : (E0 × F2) →ₗ[F2] F => f (X.comp eE.symm.toLinearMap)) =
      pointShuffleTransport eA (smallComponent ι f) := by
  have he : eE.symm.toLinearMap.comp (ι.comp (pointShuffle eA).toLinearMap) =
      pointLift κ := by
    rw [← halign]
    apply LinearMap.ext
    intro x
    simp
  have htransport := smallComponent_ambient_transport
    (E := E) (E' := E0 × F2) (F := F) (I := (A0 × I) × F2)
    eE.symm (ι.comp (pointShuffle eA).toLinearMap) f
  rw [he] at htransport
  rw [htransport]
  funext X
  exact smallComponent_precomp_equiv (I := (A0 × I) × F2) (I' := A × I)
    (E := E) (F := F) (pointShuffle eA) ι f X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E0]
  [FiniteDimensional F2 F] [FiniteDimensional F2 A]
  [FiniteDimensional F2 A0] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] (E0 × F2))]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (((A0 × I) × F2) →ₗ[F2] F)] in
/-- The original partially fixed small function is literally the function
appearing on the left side of the actual one-point mixed recurrence. -/
theorem partialRestrict_smallComponent_mixed_aligned (ι : (A × I) →ₗ[F2] E)
    (eA : (A0 × F2) ≃ₗ[F2] A) (eE : (E0 × F2) ≃ₗ[F2] E)
    (κ : (A0 × I) →ₗ[F2] E0)
    (halign : eE.toLinearMap.comp (pointLift κ) =
      ι.comp (pointShuffle eA).toLinearMap)
    (f : (E →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict (smallComponent ι f) a =
      partialRestrict (pointRestrict (smallComponent (pointLift κ)
        (fun X : (E0 × F2) →ₗ[F2] F => f (X.comp eE.symm.toLinearMap)))
        (a (eA (0, 1))))
        ((a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)) := by
  rw [smallComponent_mixed_aligned ι eA eE κ halign f,
    partialRestrict_pointRestrict_pointShuffleTransport]

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The complete fixed-point induction from the fixed-character base estimate.
The base is kept as a named mathematical input here so its separate character
induction can be assembled independently. This intermediate theorem is not
the final KMS endpoint: its base must be discharged by the proved homogeneous
character estimate. All point-recursion, basis transport and local-density
steps are established within this theorem's proof.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

variable {F : Type v} {I J : Type u}
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 F] [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Fintype F] [Fintype I] [Fintype J]

omit [FiniteDimensional F2 J] [Fintype J] in
/-- The actual mixed norm for arbitrary prescribed fixed points. The rank cap
and scalar constants are chosen before either ambient dimension. -/
theorem mixed_bound_of_character_bound (R : ℕ) (H ε : ℝ)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J)
    (hπ : Function.Surjective π)
    (hbase : ∀ (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E],
      ∀ (ι : I →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 I) ε f →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        fixedFrequencyEnergy ι f π ν ≤ H * ε) :
    ∀ (n : ℕ) (E : Type u) [AddCommGroup E] [Module F2 E]
      [FiniteDimensional F2 E] [Fintype E]
      (A : Type u) [AddCommGroup A] [Module F2 A]
      [FiniteDimensional F2 A] [Fintype A],
      Module.finrank F2 A = n →
      ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
      ∀ (f : (E →ₗ[F2] F) → ℝ), KMSBasisInvariant.IsBasisInvariant f →
      AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f →
      ∀ (a : A →ₗ[F2] F), Module.finrank F2 A + Module.finrank F2 I ≤ R →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
          H * mixedStepFactor R ^ n * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ A _ _ _ _ hAn ι hι f hf hd a hr
    by_cases hn : n = 0
    · have hz : Module.finrank F2 A = 0 := hAn.trans hn
      let : Subsingleton A := Module.finrank_zero_iff.mp hz
      have hi : Function.Injective (ι.comp (LinearMap.inr F2 A I)) := by
        intro x y hxy
        exact congrArg Prod.snd (hι hxy)
      have hd0 : AffineDensityBound (Module.finrank F2 I) ε f := by simpa [hz] using hd
      rw [mixedEnergy_zeroFixed]
      simpa only [hn, pow_zero, mul_one] using
        hbase E (ι.comp (LinearMap.inr F2 A I)) hi f hf hd0
    · have hp : 0 < Module.finrank F2 A := by omega
      obtain ⟨A0, eA, hAdrop⟩ := KMSPointComplement.exists_point_equiv hp
      change Module.finrank F2 A0 + 1 = Module.finrank F2 A at hAdrop
      obtain ⟨E0, eE, κ, hκ, halign⟩ := exists_mixed_aligned_point ι hι eA
      let f' : ((E0 × F2) →ₗ[F2] F) → ℝ :=
        fun X => f (X.comp eE.symm.toLinearMap)
      let a0 : A0 →ₗ[F2] F := (a.comp eA.toLinearMap).comp (LinearMap.inl F2 A0 F2)
      let b : F := a (eA (0, 1))
      let r0 := Module.finrank F2 A0 + Module.finrank F2 I
      let t := Module.finrank F2 I + Module.finrank F2 J
      have hs : Module.finrank F2 A0 < n := by omega
      have hr0 : r0 ≤ R := by dsimp [r0]; omega
      have hf' : KMSBasisInvariant.IsBasisInvariant f' :=
        ambient_basisInvariant_transport eE.symm f hf
      have hd' : AffineDensityBound (r0 + 1) ε f' := by
        have h := AffineDensityBound.domain_equiv _ ε f hd eE.symm
        have he : Module.finrank F2 A + Module.finrank F2 I = r0 + 1 := by
          dsimp [r0]; omega
        simpa only [he] using h
      have hdp : AffineDensityBound r0 ε (pointRestrict f' b) :=
        AffineDensityBound.pointRestrict r0 ε f' hd' b
      have hdo : AffineDensityBound r0 ε f' :=
        AffineDensityBound.mono (Nat.le_succ r0) ε f' hd'
      have hdimE : Module.finrank F2 E = Module.finrank F2 E0 + 1 := by
        simpa only [Module.finrank_prod, Module.finrank_self] using eE.finrank_eq.symm
      have ht : t ≤ 2 * R := by
        have hji : Module.finrank F2 J ≤ Module.finrank F2 I :=
          LinearMap.finrank_le_finrank_of_surjective hπ
        dsimp [t]
        omega
      have hcard : (Fintype.card ((A0 × I) →ₗ[F2] F2) : ℝ) = (2 : ℝ) ^ r0 := by
        rw [Module.card_eq_pow_finrank (K := F2)]
        simp [Module.finrank_prod, r0, F2, ZMod.card]
      let C := H * mixedStepFactor R ^ Module.finrank F2 A0 * ε
      let W0 : ℝ := 2 ^ (t * Module.finrank F2 E0)
      let W1 : ℝ := 2 ^ (t * (Module.finrank F2 E0 + 1))
      have hW0 : 0 < W0 := by dsimp [W0]; positivity
      have hW1 : 0 < W1 := by dsimp [W1]; positivity
      have hfirst : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent κ (pointRestrict f' b)) a0) ≤ C / W0 := by
        apply (le_div_iff₀ hW0).mpr
        have h := ih (Module.finrank F2 A0) hs E0 A0 rfl κ hκ
          (pointRestrict f' b) (pointRestrict_invariant f' hf' b) hdp a0 hr0
        simpa only [C, W0, t, mul_comm] using h
      have hsecond (a' : A0 →ₗ[F2] F) : sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent (pointPad κ) f') a') ≤ C / W1 := by
        apply (le_div_iff₀ hW1).mpr
        have h := ih (Module.finrank F2 A0) hs (E0 × F2) A0 rfl
          (pointPad κ) (pointPad_injective κ hκ) f' hf' hdo a' hr0
        simpa only [C, W1, t, Module.finrank_prod, Module.finrank_self, mul_comm] using h
      have hrec := mixed_point_sliceEnergy_le_of_bounds κ hκ f' hf' a0 b
        (fun T => π.comp T = ν) (C / W0) (C / W1) hfirst hsecond
      rw [hcard] at hrec
      have hweighted := mixed_weighted_step_pow R (Module.finrank F2 A0)
        (Module.finrank F2 E0) t r0 H ε _ (C / W0) (C / W1)
        hH hε ht hr0 hrec
        (by change W0 * (C / W0) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW0)])
        (by change W1 * (C / W1) ≤ C; rw [mul_div_cancel₀ _ (ne_of_gt hW1)])
      rw [partialRestrict_smallComponent_mixed_aligned ι eA eE κ halign f a]
      simpa only [hdimE, ← hAn, ← hAdrop, f', a0, b, t] using hweighted

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v
attribute [local instance] mapFintype

variable {E A I J : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 A]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J] [FiniteDimensional F2 F]
  [Fintype E] [Fintype A] [Fintype I] [Fintype J] [Fintype F]

/-- KMS's mixed bound with an explicit safe rank-dependent constant. Fixed
points and fixed characters are arbitrary; their independence is not assumed. -/
theorem mixed_slice_bound (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ Module.finrank F2 A * ε := by
  have hi : Module.finrank F2 I ≤ R := by omega
  have hpow : (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) ≤
      2 ^ (4 * R * R) := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hi) hi
  apply mixed_bound_of_character_bound R ((2 : ℝ) ^ (4 * R * R)) ε
    (by positivity) hε π ν hπ ?_ (Module.finrank F2 A) E A rfl ι hι f hf hd a hr
  intro E' _ _ _ _ κ hκ g hg hgd
  exact (fixedFrequencyEnergy_le_of_homogeneous κ hκ g hg ε
    (AffineDensityBound.homogeneous _ ε g hgd) π hπ ν).trans
      (mul_le_mul_of_nonneg_right hpow hε)

/-- A single uniform constant for all fixed-point dimensions at rank at most R. -/
def mixedRankConstant (R : ℕ) : ℝ := (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ R

theorem mixedRankConstant_nonneg (R : ℕ) : 0 ≤ mixedRankConstant R := by
  unfold mixedRankConstant
  exact mul_nonneg (by positivity) (pow_nonneg (mixedStepFactor_nonneg R) _)

theorem mixed_slice_bound_uniform (R : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ι : (A × I) →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound (Module.finrank F2 A + Module.finrank F2 I) ε f)
    (a : A →ₗ[F2] F) (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (ν : F →ₗ[F2] J) (hr : Module.finrank F2 A + Module.finrank F2 I ≤ R) :
    (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
      sliceEnergy (fun T => π.comp T = ν) (partialRestrict (smallComponent ι f) a) ≤
        mixedRankConstant R * ε := by
  apply (mixed_slice_bound R ε hε ι hι f hf hd a π hπ ν hr).trans
  unfold mixedRankConstant
  have hp : mixedStepFactor R ^ Module.finrank F2 A ≤ mixedStepFactor R ^ R :=
    pow_le_pow_right₀ (one_le_mixedStepFactor R) (by omega)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) hε

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

universe u v w

/-- A consistent finite enumeration of actual binary linear maps, built from
the finite vertex spaces. This is the enumeration used by the mixed theorem. -/
@[instance_reducible] def mixedMapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

/-- All mixed small-component slices of total degree at most `r`, with their
exact ambient normalization weight. No Hybrid derivative bound is included
in this property. Fixed primal points and prescribed frequencies are arbitrary. -/
def UniformMixedBound (r : ℕ) (L : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A I J : Type u)
    [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A] [Fintype A]
    [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I] [Fintype I]
    [AddCommGroup J] [Module F2 J] [FiniteDimensional F2 J] [Fintype J],
    ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
    ∀ (a : A →ₗ[F2] F) (π : I →ₗ[F2] J), Function.Surjective π →
    ∀ (ν : F →ₗ[F2] J), Module.finrank F2 A + Module.finrank F2 I ≤ r →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent ι f) a) ≤ L

section Transport

variable {E' : Type u} {F' : Type w}
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype E'] [Fintype F']

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- Ambient and codomain coordinate pullback preserves every actual mixed
slice, while the exponent is unchanged by ambient dimension invariance. -/
theorem UniformMixedBound.pullback {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (hf : UniformMixedBound r L f) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι u π hπ ν hr
  rw [sliceEnergy_partialRestrict_smallComponent_pullback a b ι f π ν u,
    a.finrank_eq]
  exact hf A I J (a.toLinearMap.comp ι) (a.injective.comp hι)
    (b.toLinearMap.comp u) π hπ (ν.comp b.symm.toLinearMap) hr

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- The uniform mixed property is independent of both ambient coordinate
choices. The reverse direction is pullback by the inverse equivalences. -/
theorem UniformMixedBound.pullback_iff {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) ↔
      UniformMixedBound r L f := by
  constructor
  · intro hf
    have h := UniformMixedBound.pullback a.symm b.symm
      (fun M => f (LinearEquiv.arrowCongr a b M)) hf
    have he : (fun M : E' →ₗ[F2] F' =>
        f (LinearEquiv.arrowCongr a b (LinearEquiv.arrowCongr a.symm b.symm M))) = f := by
      funext M
      apply congrArg f
      apply LinearMap.ext
      intro x
      change b (b.symm (M (a (a.symm x)))) = M x
      simp
    rw [he] at h
    exact h
  · exact UniformMixedBound.pullback a b f

end Transport

/-- The proved KMS mixed estimate discharges every instance of the uniform
mixed property. Only the actual affine density and basis-invariance
hypotheses remain; no Fourier or Hybrid estimate is supplied as a premise. -/
theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound r ε f) :
    UniformMixedBound r (mixedRankConstant r * ε) f := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι a π hπ ν hr
  exact mixed_slice_bound_uniform r ε hε ι hι f hf
    (AffineDensityBound.mono hr ε f hd) a π hπ ν hr

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
