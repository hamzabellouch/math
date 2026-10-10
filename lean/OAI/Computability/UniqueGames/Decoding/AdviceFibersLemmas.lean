import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.MatrixEnergy
import OAI.Computability.UniqueGames.Analysis.MatrixNoiseLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixParityRow
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas

namespace OAI

section

/-!
# Exact visible row advice and private matrix coordinates

Every nonempty fiber of `M ↦ A ∘ M` is an affine copy of
`Hom(E, ker A)`, whether or not `A` is surjective.  Choosing one base matrix
for each attainable row gives a product decomposition of the complete matrix
space.  Uniform sampling therefore makes visible row advice and the hidden
kernel-valued matrix independent.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear

namespace UniqueGamesTheorem.Decoder.AdviceFibers

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K]
  [AddCommGroup R] [Module F2 R]

/-- Actual matrices with the specified observed row advice. -/
abbrev RowFiber (A : K →ₗ[F2] R) (S : E →ₗ[F2] R) :=
  {M : E →ₗ[F2] K // A.comp M = S}

/-- Hidden coordinates relative to one base matrix in the same row fiber. -/
def kernelDifference (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) :
    E →ₗ[F2] A.ker :=
  (M.val - M₀).codRestrict A.ker (by
    intro x
    change A (M.val x - M₀ x) = 0
    rw [map_sub]
    have hM := LinearMap.congr_fun M.property x
    have hbase := LinearMap.congr_fun h₀ x
    change A (M.val x) = S x at hM
    change A (M₀ x) = S x at hbase
    rw [hM, hbase, sub_self])

@[simp] theorem kernelDifference_apply (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) (x : E) :
    (kernelDifference A S M₀ h₀ M x : K) = M.val x - M₀ x := rfl

/-- Reassemble an actual matrix from its fixed visible base and private part. -/
def assemble (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) : E →ₗ[F2] K :=
  M₀ + A.ker.subtype.comp N

@[simp] theorem assemble_apply (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (x : E) :
    assemble A M₀ N x = M₀ x + (N x : K) := rfl

/-- Observed advice is completely unchanged by the private coordinates. -/
theorem observed_assemble (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) : A.comp (assemble A M₀ N) = A.comp M₀ := by
  ext x
  have hN : A (N x : K) = 0 := (N x).property
  simp only [LinearMap.comp_apply, assemble_apply, map_add, hN, add_zero]

/-- The exact row-fiber bijection; no rank or surjectivity premise is needed. -/
def rowFiberEquiv (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) :
    (E →ₗ[F2] A.ker) ≃ RowFiber A S where
  toFun N := ⟨assemble A M₀ N, (observed_assemble A M₀ N).trans h₀⟩
  invFun := kernelDifference A S M₀ h₀
  left_inv N := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M₀ x + (N x : K) - M₀ x = (N x : K)
    exact add_sub_cancel_left _ _
  right_inv M := by
    apply Subtype.ext
    ext x
    change M₀ x + (M.val x - M₀ x) = M.val x
    simpa only [← add_sub_assoc] using add_sub_cancel_left (M₀ x) (M.val x)

@[simp] theorem rowFiberEquiv_coe (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (N : E →ₗ[F2] A.ker) :
    (rowFiberEquiv A S M₀ h₀ N).val = assemble A M₀ N := rfl

@[simp] theorem rowFiberEquiv_symm (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) :
    (rowFiberEquiv A S M₀ h₀).symm M = kernelDifference A S M₀ h₀ M := rfl

/-- Affine target intercepts are retained in the private coordinates. -/
theorem assemble_affine_target (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (z : E) (u : K) :
    assemble A M₀ N z + u = (N z : K) + (M₀ z + u) := by
  rw [assemble_apply]
  ac_rfl

section UniformFiber

variable (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
  [Fintype (E →ₗ[F2] A.ker)]

theorem rowFiber_card (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) :
    Nat.card (RowFiber A S) = Fintype.card (E →ₗ[F2] A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A S M₀ h₀).symm, Nat.card_eq_fintype_card]

/-- Uniform private matrices push forward to uniform matrices in the fiber. -/
theorem rowFiber_expect (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S)
    [Fintype (RowFiber A S)] (f : (E →ₗ[F2] K) → ℝ) :
    (𝔼 M : RowFiber A S, f M.val) =
      𝔼 N : E →ₗ[F2] A.ker, f (assemble A M₀ N) := by
  exact (Fintype.expect_equiv (rowFiberEquiv A S M₀ h₀)
    (fun N => f (assemble A M₀ N)) (fun M => f M.val) (fun _ => rfl)).symm

end UniformFiber

/-- Only attainable rows are observation values. -/
abbrev ObservedRow (A : K →ₗ[F2] R) :=
  {S : E →ₗ[F2] R // ∃ M : E →ₗ[F2] K, A.comp M = S}

def observe (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) : ObservedRow (E := E) A :=
  ⟨A.comp M, M, rfl⟩

/-- A canonical base depends only on observed advice, never on the hidden matrix. -/
def observedBase (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A) : E →ₗ[F2] K :=
  Classical.choose S.property

theorem observedBase_property (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A) :
    A.comp (observedBase A S) = S.val := Classical.choose_spec S.property

def hiddenCoordinate (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) :
    E →ₗ[F2] A.ker :=
  (rowFiberEquiv A (observe A M).val (observedBase A (observe A M))
    (observedBase_property A (observe A M))).symm ⟨M, rfl⟩

theorem observe_assemble_base (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A)
    (N : E →ₗ[F2] A.ker) : observe A (assemble A (observedBase A S) N) = S := by
  apply Subtype.ext
  exact (observed_assemble A (observedBase A S) N).trans (observedBase_property A S)

/-- Full matrix space is a product of attainable visible rows and private
kernel-valued maps.  A section of `A` is not required. -/
def observationEquiv (A : K →ₗ[F2] R) :
    (E →ₗ[F2] K) ≃ ObservedRow (E := E) A × (E →ₗ[F2] A.ker) where
  toFun M := (observe A M, hiddenCoordinate A M)
  invFun p := assemble A (observedBase A p.1) p.2
  left_inv M := by
    exact congrArg Subtype.val
      ((rowFiberEquiv A (observe A M).val (observedBase A (observe A M))
        (observedBase_property A (observe A M))).apply_symm_apply ⟨M, rfl⟩)
  right_inv p := by
    apply Prod.ext
    · exact observe_assemble_base A p.1 p.2
    · apply LinearMap.ext
      intro x
      apply Subtype.ext
      change assemble A (observedBase A p.1) p.2 x -
        observedBase A (observe A (assemble A (observedBase A p.1) p.2)) x =
          (p.2 x : K)
      rw [observe_assemble_base, assemble_apply]
      exact add_sub_cancel_left _ _

@[simp] theorem observationEquiv_apply (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) :
    observationEquiv A M = (observe A M, hiddenCoordinate A M) := rfl

section UniformObservation

variable (A : K →ₗ[F2] R)
  [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] A.ker)] [Fintype (ObservedRow (E := E) A)]

/-- The joint law is exactly the uniform product law. -/
theorem observation_expect (f : ObservedRow (E := E) A → (E →ₗ[F2] A.ker) → ℝ) :
    (𝔼 M : E →ₗ[F2] K, f (observe A M) (hiddenCoordinate A M)) =
      𝔼 S : ObservedRow (E := E) A, 𝔼 N : E →ₗ[F2] A.ker, f S N := by
  rw [Fintype.expect_equiv (observationEquiv A)
    (fun M => f (observe A M) (hiddenCoordinate A M))
    (fun p => f p.1 p.2) (fun _ => rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- Exact factorization of every product of visible and private observables. -/
theorem observed_hidden_independent (f : ObservedRow (E := E) A → ℝ)
    (g : (E →ₗ[F2] A.ker) → ℝ) :
    (𝔼 M : E →ₗ[F2] K, f (observe A M) * g (hiddenCoordinate A M)) =
      (𝔼 S : ObservedRow (E := E) A, f S) * (𝔼 N : E →ₗ[F2] A.ker, g N) := by
  rw [observation_expect A (fun S N => f S * g N)]
  simp_rw [← Finset.mul_expect]
  exact (Finset.expect_mul _ _ _).symm

end UniformObservation

end UniqueGamesTheorem.Decoder.AdviceFibers

end

end

section

/-!
# Finite latent samplers and their actual spectral law

This bridge counts all sampler outcomes, including repeated vectors and the
zero vector.  Uniform sampler detection is exactly the complement of the
matrix operator's annihilation multiplier.
-/

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixNoise

namespace UniqueGamesTheorem.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

/-- The real pushforward of the uniform law on sampler outcomes. -/
def samplerLaw (noise : Noise → V) (v : V) : ℝ := by
  classical
  exact ∑ n, if noise n = v then (Fintype.card Noise : ℝ)⁻¹ else 0

omit [Fintype V] in
theorem samplerLaw_nonneg (noise : Noise → V) (v : V) :
    0 ≤ samplerLaw noise v := by
  classical
  unfold samplerLaw
  apply Finset.sum_nonneg
  intro n _
  split_ifs <;> positivity

omit [Fintype V] in
/-- Literal counting formula; multiple sampler outcomes mapping to the same
vector retain their multiplicity. -/
theorem samplerLaw_eq_count (noise : Noise → V) (v : V) :
    samplerLaw noise v =
      ((Finset.univ.filter fun n => noise n = v).card : ℝ) / Fintype.card Noise := by
  classical
  unfold samplerLaw
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem samplerLaw_sum (noise : Noise → V) (f : V → ℝ) :
    (∑ v, samplerLaw noise v * f v) =
      (Fintype.card Noise : ℝ)⁻¹ * ∑ n, f (noise n) := by
  classical
  unfold samplerLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (Finset.mul_sum _ _ _).symm

/-- Exact pushforward expectation, with the uniform normalization explicit. -/
theorem sample_expect_eq (noise : Noise → V) (f : V → ℝ) :
    (𝔼 n, f (noise n)) = ∑ v, samplerLaw noise v * f v := by
  rw [samplerLaw_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]

theorem samplerLaw_normalized [Nonempty Noise] (noise : Noise → V) :
    ∑ v, samplerLaw noise v = 1 := by
  have h := sample_expect_eq noise (fun _ => 1)
  simpa using h.symm

theorem rat_expect_cast (f : Noise → ℚ) :
    ((𝔼 n, f n : ℚ) : ℝ) = 𝔼 n, (f n : ℝ) := by
  simp only [Finset.expect_eq_sum_div_card, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

omit [Fintype V] in
theorem samplerLaw_eq_rat_count (noise : Noise → V) (v : V) :
    samplerLaw noise v =
      ((((Finset.univ.filter fun n => noise n = v).card : ℚ) /
        (Fintype.card Noise : ℚ) : ℚ) : ℝ) := by
  rw [samplerLaw_eq_count]
  simp only [Rat.cast_div, Rat.cast_natCast]

end FiniteLaw

section ActualMultiplier

variable {Noise V E : Type*} [Fintype Noise] [Fintype V]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup E] [Module F2 E]

/-- The actual matrix multiplier is precisely the sampler's kernel event. -/
theorem sample_kernel_eq_eigenvalue (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) = 0 then (1 : ℝ) else 0) =
      linearNoiseEigenvalue (samplerLaw noise) S := by
  classical
  exact sample_expect_eq noise (fun v => if S v = 0 then 1 else 0)

/-- Detection plus annihilation is one for the same unconditional sampler. -/
theorem detection_add_eigenvalue [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) +
      linearNoiseEigenvalue (samplerLaw noise) S = 1 := by
  classical
  rw [← sample_kernel_eq_eigenvalue, ← Finset.expect_add_distrib]
  calc
    _ = 𝔼 _n : Noise, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro n _
      by_cases h : S (noise n) = 0 <;> simp [h]
    _ = 1 := Fintype.expect_const 1

/-- The constant-detection input becomes the `7/8` multiplier bound. -/
theorem detection_eigenvalue_le [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E)
    (hdetect : (1 : ℝ) / 8 ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 7 / 8 := by
  have h := detection_add_eigenvalue noise S
  linarith

/-- A generic detection level bounds the annihilation multiplier. -/
theorem detection_eigenvalue_le_complement [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E) (d : ℝ)
    (hdetect : d ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 1 - d := by
  have h := detection_add_eigenvalue noise S
  linarith

/-- The gadget may keep its finite probabilities rational throughout. -/
theorem rational_detection_eigenvalue_le [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E)
    (hdetect : (1 : ℚ) / 8 ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℚ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 7 / 8 := by
  apply detection_eigenvalue_le noise S
  have hcast := (Rat.cast_le (K := ℝ)).mpr hdetect
  rw [rat_expect_cast] at hcast
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero,
    apply_ite] using hcast

end ActualMultiplier

end UniqueGamesTheorem.Decoder.NoiseSampler

end

end

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace UniqueGamesTheorem.Decoder.PositiveMultiplier

section FiniteSpectra

variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

/-- A `7/8` bound outside the retained set forces at least `0.92` retained
mass when acceptance is at least `0.99`.  The statement keeps the exact
rational constants, rather than assuming a low-rank mass premise. -/
theorem retained_mass_of_acceptance
    (w : J → ℝ) (a lam : (j : J) → I j → ℝ)
    (keep : (j : J) → I j → Prop)
    (hw : ∀ j, 0 ≤ w j) (htotal : energy w a = 1)
    (hone : ∀ j i, lam j i ≤ 1)
    (hhigh : ∀ j i, ¬ keep j i → lam j i ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ spectralEnergy w lam a) :
    (23 : ℝ) / 25 ≤ cutoffEnergy w keep a := by
  classical
  have hp (j : J) (i : I j) :
      lam j i * a j i ^ 2 ≤ (7 / 8 : ℝ) * a j i ^ 2 +
        (1 / 8 : ℝ) * (if keep j i then a j i ^ 2 else 0) := by
    by_cases hk : keep j i
    · have h := mul_le_mul_of_nonneg_right (hone j i) (sq_nonneg (a j i))
      simp only [ite_eq_left hk] at *
      nlinarith
    · have h := mul_le_mul_of_nonneg_right (hhigh j i hk) (sq_nonneg (a j i))
      simpa only [ite_eq_right hk, mul_zero, add_zero] using h
  have hb : spectralEnergy w lam a ≤
      (7 / 8 : ℝ) * energy w a + (1 / 8 : ℝ) * cutoffEnergy w keep a := by
    calc
      _ ≤ ∑ j, w j * ∑ i, ((7 / 8 : ℝ) * a j i ^ 2 +
          (1 / 8 : ℝ) * (if keep j i then a j i ^ 2 else 0)) := by
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hp j i)) (hw j))
      _ = _ := by
        simp only [energy, cutoffEnergy, Finset.sum_add_distrib,
          Finset.mul_sum, mul_add]
        congr 1 <;>
          (apply Finset.sum_congr rfl
           intro j _
           apply Finset.sum_congr rfl
           intro i _
           ring)
  rw [htotal] at hb
  linarith

theorem positive_multiplier_comparison
    (w : J → ℝ) (a lam τ : (j : J) → I j → ℝ)
    (keep : (j : J) → I j → Prop) (t : ℝ)
    (hw : ∀ j, 0 ≤ w j) (htotal : energy w a = 1) (ht : 0 ≤ t)
    (hone : ∀ j i, lam j i ≤ 1)
    (hhigh : ∀ j i, ¬ keep j i → lam j i ≤ 7 / 8)
    (hτ : ∀ j i, 0 ≤ τ j i)
    (hlow : ∀ j i, keep j i → t ≤ τ j i)
    (haccept : (99 : ℝ) / 100 ≤ spectralEnergy w lam a) :
    (9 : ℝ) / 10 * t ≤ spectralEnergy w τ a := by
  classical
  have hmass := retained_mass_of_acceptance w a lam keep hw htotal hone hhigh haccept
  have hp (j : J) (i : I j) :
      t * (if keep j i then a j i ^ 2 else 0) ≤ τ j i * a j i ^ 2 := by
    by_cases hk : keep j i
    · simpa only [ite_eq_left hk] using
        mul_le_mul_of_nonneg_right (hlow j i hk) (sq_nonneg (a j i))
    · simpa only [ite_eq_right hk, mul_zero] using mul_nonneg (hτ j i) (sq_nonneg (a j i))
  have hb : t * cutoffEnergy w keep a ≤ spectralEnergy w τ a := by
    unfold cutoffEnergy spectralEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      t * (w j * ∑ i, if keep j i then a j i ^ 2 else 0) =
          w j * (∑ i, t * (if keep j i then a j i ^ 2 else 0)) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hp j i)) (hw j)
  have hm := mul_le_mul_of_nonneg_left hmass ht
  nlinarith

/-- A finite probability law with mean at least `14.4 η` assigns mass at
least `10 η` to acceptances at least `4 η`. -/
theorem good_fiber_mass
    {Q : Type*} [Fintype Q] (μ p : Q → ℝ) (η : ℝ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hη : 0 ≤ η) (hp : ∀ q, p q ≤ 1)
    (hmean : (72 : ℝ) / 5 * η ≤ ∑ q, μ q * p q) :
    10 * η ≤ ∑ q, μ q * if 4 * η ≤ p q then 1 else 0 := by
  classical
  have hbound : (∑ q, μ q * p q) ≤
      4 * η + ∑ q, μ q * if 4 * η ≤ p q then 1 else 0 := by
    calc
      _ ≤ ∑ q, μ q * (4 * η + if 4 * η ≤ p q then 1 else 0) := by
        apply Finset.sum_le_sum
        intro q _
        apply mul_le_mul_of_nonneg_left _ (hμ q)
        split_ifs with hq
        · linarith [hp q]
        · linarith
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]
  linarith

end FiniteSpectra

section ActualMatrixTest

variable {Q C E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

/-- The actual equality test, including zero perturbation factors. -/
def equalityAcceptance (ν : V → ℝ) (label : (E →ₗ[F2] V) → C) : ℝ := by
  classical
  exact 𝔼 X, ∑ v, ν v * (𝔼 l : E →ₗ[F2] F2,
    if label X = label (X + l.smulRight v) then (1 : ℝ) else 0)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 V] [Fintype V]
  [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)] in
theorem color_pair_sum (label : (E →ₗ[F2] V) → C)
    (X Y : E →ₗ[F2] V) :
    (∑ c, colorIndicator label c X * colorIndicator label c Y) =
      if label X = label Y then (1 : ℝ) else 0 := by
  classical
  simp [colorIndicator, eq_comm]

/-- Equality acceptance has the actual positive Fourier multiplier.  Color
indicators give the same equality expansion as output characters, with no
extra factor depending on the output alphabet. -/
theorem equalityAcceptance_fourier (ν : V → ℝ)
    (label : (E →ₗ[F2] V) → C) :
    equalityAcceptance ν label =
      ∑ c, ∑ S : V →ₗ[F2] E,
        linearNoiseEigenvalue ν S * linearCoeff (colorIndicator label c) S ^ 2 := by
  classical
  simp_rw [← linearRealNoiseOperator_energy]
  rw [← Finset.expect_sum_comm]
  unfold equalityAcceptance linearRealNoiseOperator
  apply Finset.expect_congr rfl
  intro X _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  calc
    ν v * (𝔼 l : E →ₗ[F2] F2,
        if label X = label (X + l.smulRight v) then (1 : ℝ) else 0) =
      ν v * (𝔼 l : E →ₗ[F2] F2,
        ∑ c, colorIndicator label c X * colorIndicator label c (X + l.smulRight v)) := by
          simp only [color_pair_sum]
    _ = _ := by
      rw [Finset.expect_sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_expect]
      ring

/-- Spectral comparison applied to a genuine family of matrix labelings.
The two explicit probability laws may be the latent gadget law and uniform
sampling in the distinguished subspace, respectively. -/
theorem matrix_test_comparison
    (μ : Q → ℝ) (ν ρ : V → ℝ)
    (label : Q → (E →ₗ[F2] V) → C)
    (keep : (V →ₗ[F2] E) → Prop) (t : ℝ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hν : ∀ v, 0 ≤ ν v) (hνsum : ∑ v, ν v = 1)
    (hρ : ∀ v, 0 ≤ ρ v) (ht : 0 ≤ t)
    (hhigh : ∀ S : V →ₗ[F2] E, ¬ keep S → linearNoiseEigenvalue ν S ≤ 7 / 8)
    (hlow : ∀ S : V →ₗ[F2] E, keep S → t ≤ linearNoiseEigenvalue ρ S)
    (haccept : (99 : ℝ) / 100 ≤ ∑ q, μ q * equalityAcceptance ν (label q)) :
    (9 : ℝ) / 10 * t ≤ ∑ q, μ q * equalityAcceptance ρ (label q) := by
  have hs (law : V → ℝ) :
      spectralEnergy (fun qc : Q × C => μ qc.1)
        (fun _ S => linearNoiseEigenvalue law S) (labelingCoeff label) =
          ∑ q, μ q * equalityAcceptance law (label q) := by
    simp only [spectralEnergy, labelingCoeff, Fintype.sum_prod_type,
      equalityAcceptance_fourier, Finset.mul_sum]
  rw [← hs] at haccept ⊢
  apply positive_multiplier_comparison
    (fun qc : Q × C => μ qc.1) (labelingCoeff label)
    (fun _ S => linearNoiseEigenvalue ν S)
    (fun _ S => linearNoiseEigenvalue ρ S) (fun _ S => keep S) t
  · exact fun qc => hμ qc.1
  · exact labelingCoeff_energy_one μ label hμsum
  · exact ht
  · exact fun _ S => linearNoiseEigenvalue_le_one ν S hν hνsum
  · exact fun _ S hS => hhigh S hS
  · exact fun _ S => linearNoiseEigenvalue_nonneg ρ S hρ
  · exact fun _ S hS => hlow S hS
  · exact haccept

end ActualMatrixTest

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

/-- Pushforward of uniform sampling in `K`.  For a subspace inclusion this
is uniform sampling in that subspace; the definition also permits a linear
map with nontrivial fibers without accidentally conditioning on nonzero vectors. -/
def subspaceLaw (ι : K →ₗ[F2] V) (v : V) : ℝ := by
  classical
  exact ∑ k, if ι k = v then (Fintype.card K : ℝ)⁻¹ else 0

omit [FiniteDimensional F2 K] [Fintype V] in
theorem subspaceLaw_nonneg (ι : K →ₗ[F2] V) (v : V) :
    0 ≤ subspaceLaw ι v := by
  classical
  unfold subspaceLaw
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

omit [FiniteDimensional F2 K] in
theorem subspaceLaw_sum (ι : K →ₗ[F2] V) (f : V → ℝ) :
    (∑ v, subspaceLaw ι v * f v) = (Fintype.card K : ℝ)⁻¹ * ∑ k, f (ι k) := by
  classical
  unfold subspaceLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (Finset.mul_sum _ _ _).symm

omit [FiniteDimensional F2 K] in
theorem subspaceLaw_normalized (ι : K →ₗ[F2] V) :
    ∑ v, subspaceLaw ι v = 1 := by
  have h := subspaceLaw_sum ι (fun _ => 1)
  simpa [Fintype.card_ne_zero] using h

theorem subspaceLaw_eigenvalue (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E) :
    linearNoiseEigenvalue (subspaceLaw ι) S =
      ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ := by
  classical
  let k := (Finset.univ.filter fun x : K => S (ι x) = 0).card
  have hs : (∑ x : K, if S (ι x) = 0 then (1 : ℝ) else 0) = (k : ℝ) := by
    rw [← Finset.sum_filter]
    simp [k]
  have hc : (k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
      (Fintype.card K : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (UniqueGamesTheorem.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, LinearMap.comp_apply] using h
  have hn : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold linearNoiseEigenvalue
  rw [subspaceLaw_sum, hs]
  apply mul_right_cancel₀ hp
  calc
    ((Fintype.card K : ℝ)⁻¹ * (k : ℝ)) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
        (Fintype.card K : ℝ)⁻¹ * ((k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range) :=
      mul_assoc _ _ _
    _ = (Fintype.card K : ℝ)⁻¹ * (Fintype.card K : ℝ) := by rw [hc]
    _ = 1 := inv_mul_cancel₀ hn
    _ = ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ *
        (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range := (inv_mul_cancel₀ hp).symm

theorem subspaceLaw_eigenvalue_lower (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E)
    (r : ℕ) (hr : Module.finrank F2 (S.comp ι).range < r) :
    ((2 : ℝ) ^ r)⁻¹ ≤ linearNoiseEigenvalue (subspaceLaw ι) S := by
  rw [subspaceLaw_eigenvalue, ← one_div, ← one_div]
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hr)

end UniformSubspace

section ManuscriptComparison

variable {Q C K E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

theorem matrix_spectral_comparison
    (μ : Q → ℝ) (ν : V → ℝ) (ι : K →ₗ[F2] V)
    (label : Q → (E →ₗ[F2] V) → C) (r : ℕ)
    (hμ : ∀ q, 0 ≤ μ q) (hμsum : ∑ q, μ q = 1)
    (hν : ∀ v, 0 ≤ ν v) (hνsum : ∑ v, ν v = 1)
    (hdetect : ∀ S : V →ₗ[F2] E,
      r ≤ Module.finrank F2 (S.comp ι).range → linearNoiseEigenvalue ν S ≤ 7 / 8)
    (haccept : (99 : ℝ) / 100 ≤ ∑ q, μ q * equalityAcceptance ν (label q)) :
    (9 : ℝ) / 10 * ((2 : ℝ) ^ r)⁻¹ ≤
      ∑ q, μ q * equalityAcceptance (subspaceLaw ι) (label q) := by
  apply matrix_test_comparison μ ν (subspaceLaw ι) label
    (fun S => Module.finrank F2 (S.comp ι).range < r) ((2 : ℝ) ^ r)⁻¹
    hμ hμsum hν hνsum (subspaceLaw_nonneg ι)
  · positivity
  · intro S hS
    exact hdetect S (Nat.le_of_not_gt hS)
  · intro S hS
    exact subspaceLaw_eigenvalue_lower ι S r hS
  · exact haccept

end ManuscriptComparison

end UniqueGamesTheorem.Decoder.PositiveMultiplier

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Decoder.PrivateFourier

open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixParity
open UniqueGamesTheorem.Fourier.MatrixParityRow
open scoped BigOperators Classical

section Signs

/-- A real-valued binary character, with the uniform Fourier normalization. -/
def sign (a : F2) : ℝ := (binarySign a).re

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_sq (a : F2) : sign a ^ 2 = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

@[simp] theorem sign_abs (a : F2) : |sign a| = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  simp [sign, binarySign_add, Complex.mul_re]

theorem sign_add_one (a : F2) : sign (a + 1) = -sign a := by
  rw [sign_add, sign_one]
  ring

end Signs

section CharacterAverages

variable {H K : Type*} [AddCommGroup H] [Module F2 H]
    [AddCommGroup K] [Module F2 K]

theorem binary_neg_eq_self (x : K) : -x = x := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hh := congrArg (fun a : F2 => a • x) htwo
  exact neg_eq_iff_add_eq_zero.mpr
    (by simpa only [add_smul, one_smul, zero_smul] using hh)

theorem binary_add_eq_zero_iff (x y : K) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg, binary_neg_eq_self]

theorem average_sign_dual [Fintype (K →ₗ[F2] F2)] (x : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x)) = if x = 0 then 1 else 0 := by
  have h := congrArg Complex.re
    (UniqueGamesTheorem.Fourier.MatrixNoise.average_evaluationCharacter x)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re, sign] using h

theorem average_sign_primal [Fintype H] (σ : H →ₗ[F2] F2) :
    (𝔼 h : H, sign (σ h)) = if σ = 0 then 1 else 0 := by
  have h := congrArg Complex.re (expect_linearFunctionalCharacter σ)
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re,
    linearFunctionalCharacter_apply, sign] using h

/-- Exact character expansion of equality in the actual output space. -/
theorem average_sign_equality [Fintype (K →ₗ[F2] F2)] (x y : K) :
    (𝔼 σ : K →ₗ[F2] F2, sign (σ x) * sign (σ y)) =
      if x = y then 1 else 0 := by
  simp_rw [← sign_add, ← map_add]
  rw [average_sign_dual, binary_add_eq_zero_iff]

/-- The ambient uniform character has trivial restriction to `H` with exactly
the reciprocal cardinality of `H`.  No conditioning on the private character
is substituted for the real experiment. -/
theorem trivial_restriction_probability [Fintype H] [Fintype (K →ₗ[F2] F2)]
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) :
    (𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0) =
      1 / (Fintype.card H : ℝ) := by
  calc
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 h : H, sign (σ (ι h)) := by
      apply Finset.expect_congr rfl
      intro σ _
      exact (average_sign_primal (σ.comp ι)).symm
    _ = 𝔼 h : H, 𝔼 σ : K →ₗ[F2] F2, sign (σ (ι h)) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 h : H, if h = 0 then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro h _
      rw [average_sign_dual]
      have heq : ι h = 0 ↔ h = 0 := by
        rw [← map_zero ι]
        exact hι.eq_iff
      rw [heq]
    _ = _ := by simp

theorem trivial_restriction_probability_pow [Fintype H]
    [FiniteDimensional F2 H] [Fintype (K →ₗ[F2] F2)]
    (ι : H →ₗ[F2] K) (hι : Function.Injective ι) :
    (𝔼 σ : K →ₗ[F2] F2, if σ.comp ι = 0 then (1 : ℝ) else 0) =
      1 / (2 : ℝ) ^ Module.finrank F2 H := by
  rw [trivial_restriction_probability ι hι]
  have hc : Fintype.card H = 2 ^ Module.finrank F2 H := by
    simpa [F2, Integration.BinaryLinear.F2, ZMod.card] using
      Module.card_fintype (Module.finBasis F2 H)
  rw [hc]
  norm_cast

end CharacterAverages

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

/-- The private sign function, formed from the table on one visible row fiber. -/
def tableSign (F : (E →ₗ[F2] H) → K) (σ : K →ₗ[F2] F2)
    (N : E →ₗ[F2] H) : ℝ := sign (σ (F N))

/-- The actual probability assigned to a reverse-map frequency. -/
def frequencyWeight (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) : ℝ :=
  linearCoeff f Φ ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
theorem frequencyWeight_nonneg (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) :
    0 ≤ frequencyWeight f Φ := sq_nonneg _

/-- Squared Fourier coefficients of the private sign form a probability law. -/
theorem tableSign_frequencyWeight_sum (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) :
    ∑ Φ : H →ₗ[F2] E, frequencyWeight (tableSign F σ) Φ = 1 := by
  simp only [frequencyWeight, linear_parseval, tableSign, sign_sq]
  exact Fintype.expect_const 1

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H]
  [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem tableSign_antifold (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (σ : K →ₗ[F2] F2) (h : H)
    (folded : ∀ N, F (N + τ.smulRight h) = F N + ι h)
    (hσ : σ (ι h) = 1) :
    ∀ N, tableSign F σ (N + τ.smulRight h) = -tableSign F σ N := by
  intro N
  simp only [tableSign, folded, map_add, hσ, sign_add_one]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
/-- Translation of the input multiplies a coefficient by its character. -/
theorem linearCoeff_translate (f : (E →ₗ[F2] H) → ℝ)
    (D : E →ₗ[F2] H) (Φ : H →ₗ[F2] E) :
    linearCoeff (fun N => f (N + D)) Φ =
      linearCoeff f Φ * (linearTraceCharacter Φ D).re := by
  have hself : D + D = 0 :=
    (linearMap_add_eq_zero_iff D D).2 rfl
  have hchange := Fintype.expect_equiv (Equiv.addRight D)
    (fun N => f (N + D) * (linearTraceCharacter Φ N).re)
    (fun N => f N * (linearTraceCharacter Φ (N + D)).re)
    (fun N => by simp only [Equiv.coe_addRight, add_assoc, hself, add_zero])
  unfold linearCoeff
  rw [hchange]
  simp only [traceCharacter_re_add, ← mul_assoc]
  exact (Finset.expect_mul _ _ _).symm

omit [FiniteDimensional F2 E] [Fintype (H →ₗ[F2] E)] in
/-- Anti-folding forces every positive-mass frequency to return first bit one. -/
theorem positive_frequency_first_bit (f : (E →ₗ[F2] H) → ℝ)
    (τ : E →ₗ[F2] F2) (h : H) (Φ : H →ₗ[F2] E)
    (folded : ∀ N, f (N + τ.smulRight h) = -f N)
    (positive : 0 < frequencyWeight f Φ) : τ (Φ h) = 1 := by
  have hcoeff : linearCoeff f Φ ≠ 0 := by
    intro hz
    simp [frequencyWeight, hz] at positive
  have heq := linearCoeff_translate f (τ.smulRight h) Φ
  have hneg : linearCoeff (fun N => f (N + τ.smulRight h)) Φ =
      -linearCoeff f Φ := by
    simp only [linearCoeff, folded, neg_mul]
    simp [Fintype.expect_eq_sum_div_card]
  rw [hneg] at heq
  have hchar : (linearTraceCharacter Φ (τ.smulRight h)).re = sign (τ (Φ h)) := by
    simp only [linearTraceCharacter_apply, linearTracePair, trace_smulRight_comp, sign]
  rw [hchar] at heq
  rcases Integration.BinaryLinear.scalar_cases (τ (Φ h)) with hz | hone
  · rw [hz, sign_zero, mul_one] at heq
    exact False.elim (hcoeff (by linarith))
  · exact hone

end ActualFourier

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

/-- Frequencies in the affine target's annihilator coset.  With `q = Q.mkQ`,
this is exactly `θ + Hom(H,Q)` in the ambient reverse-map space. -/
def frequencyCoset (q : E →ₗ[F2] V) (θ : H →ₗ[F2] E) :
    Finset (H →ₗ[F2] E) := Finset.univ.filter fun Φ => q.comp (Φ + θ) = 0

/-- Correlation on a genuine affine slice.  `N₀` is retained: its phase cannot
be discarded when the witness has a nonzero affine intercept. -/
def sliceCorrelation (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) : ℝ :=
  𝔼 A : V →ₗ[F2] H,
    f (N₀ + A.comp q) * (linearTraceCharacter θ (N₀ + A.comp q)).re

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H]
  [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
theorem traceCharacter_re_mul (Φ θ : H →ₗ[F2] E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter Φ N).re * (linearTraceCharacter θ N).re =
      (linearTraceCharacter (Φ + θ) N).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- The exact Fourier coset expansion of the affine conditional correlation. -/
theorem sliceCorrelation_eq_coset (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ =
      ∑ Φ ∈ frequencyCoset q θ,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re := by
  unfold sliceCorrelation
  calc
    _ = 𝔼 A : V →ₗ[F2] H, ∑ Φ : H →ₗ[F2] E,
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) (N₀ + A.comp q)).re := by
      apply Finset.expect_congr rfl
      intro A _
      rw [← linear_fourier_inversion f (N₀ + A.comp q), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Φ _
      rw [mul_assoc, traceCharacter_re_mul]
    _ = ∑ Φ : H →ₗ[F2] E, if q.comp (Φ + θ) = 0 then
        linearCoeff f Φ * (linearTraceCharacter (Φ + θ) N₀).re else 0 := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro Φ _
      simp only [traceCharacter_re_add, ← mul_assoc]
      rw [← Finset.mul_expect, row_character_average]
      split <;> simp
    _ = _ := by simp [frequencyCoset, Finset.sum_filter]

/-- Cauchy--Schwarz bounds an affine correlation by the actual Fourier mass
in its target coset; no spectral mass is assumed. -/
theorem sliceCorrelation_sq_le_coset_mass (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) :
    sliceCorrelation q N₀ f θ ^ 2 ≤
      (frequencyCoset q θ).card *
        ∑ Φ ∈ frequencyCoset q θ, frequencyWeight f Φ := by
  rw [sliceCorrelation_eq_coset]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (frequencyCoset q θ)
    (linearCoeff f) (fun Φ => (linearTraceCharacter (Φ + θ) N₀).re)
  have hs : ∀ Φ : H →ₗ[F2] E,
      (linearTraceCharacter (Φ + θ) N₀).re ^ 2 = 1 := by
    intro Φ
    exact sign_sq _
  simpa only [hs, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul,
    frequencyWeight, mul_comm] using hcs

end AffineSlice

section AffineEquality

variable {E H K V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K] [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)] [Fintype (K →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- The pure-tensor target character is literally evaluation at `z`. -/
theorem target_character (σ : H →ₗ[F2] F2) (z : E) (N : E →ₗ[F2] H) :
    (linearTraceCharacter (σ.smulRight z) N).re = sign (σ (N z)) := by
  simp only [linearTraceCharacter_apply, sign]
  congr 2
  rw [linearTracePair_swap]
  exact trace_smulRight_comp σ z N

omit [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Affine target equality expands into the correlations with the intercept
phase `sign (σ b)`.  In the projected experiment `b = M₀ z + u`. -/
theorem affine_equality_character_expansion (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) =
      𝔼 σ : K →ₗ[F2] F2, sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z) := by
  calc
    _ = 𝔼 A : V →ₗ[F2] H, 𝔼 σ : K →ₗ[F2] F2,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := by
      apply Finset.expect_congr rfl
      intro A _
      exact (average_sign_equality _ _).symm
    _ = 𝔼 σ : K →ₗ[F2] F2, 𝔼 A : V →ₗ[F2] H,
        sign (σ (F (N₀ + A.comp q))) *
          sign (σ (b + ι ((N₀ + A.comp q) z))) := Finset.expect_comm _ _ _
    _ = _ := by
      apply Finset.expect_congr rfl
      intro σ _
      unfold sliceCorrelation
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro A _
      simp only [map_add, sign_add, target_character, tableSign, LinearMap.comp_apply]
      ring

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
  [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] [Fintype (K →ₗ[F2] F2)] in
/-- Every slice correlation has absolute value at most one. -/
theorem sliceCorrelation_tableSign_abs_le_one (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) (θ : H →ₗ[F2] E) :
    |sliceCorrelation q N₀ (tableSign F σ) θ| ≤ 1 := by
  unfold sliceCorrelation
  calc
    _ ≤ 𝔼 A : V →ₗ[F2] H,
        |tableSign F σ (N₀ + A.comp q) *
          (linearTraceCharacter θ (N₀ + A.comp q)).re| := Finset.abs_expect_le _ _
    _ = 1 := by
      have hp (N : E →ₗ[F2] H) : |(linearTraceCharacter θ N).re| = 1 := sign_abs _
      simp only [abs_mul, tableSign, sign_abs, hp, mul_one]
      exact Fintype.expect_const 1

omit [FiniteDimensional F2 V] [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)] in
/-- Dropping the unit intercept phase can only increase the average absolute
correlation; the hypothesis is the actual affine-slice agreement probability. -/
theorem agreement_le_average_abs_correlation (q : E →ₗ[F2] V)
    (N₀ : E →ₗ[F2] H) (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (z : E) (b : K) :
    (𝔼 A : V →ₗ[F2] H,
      if F (N₀ + A.comp q) = b + ι ((N₀ + A.comp q) z) then (1 : ℝ) else 0) ≤
      𝔼 σ : K →ₗ[F2] F2,
        |sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := by
  rw [affine_equality_character_expansion]
  apply Finset.expect_le_expect
  intro σ _
  calc
    _ ≤ |sign (σ b) *
        sliceCorrelation q N₀ (tableSign F σ) ((σ.comp ι).smulRight z)| := le_abs_self _
    _ = _ := by rw [abs_mul, sign_abs, one_mul]

end AffineEquality

section CosetCardinality

variable {E H : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (H →ₗ[F2] E)]

/-- The exact number of frequencies in the affine coset.  Translation does not
alter the annihilator cardinality, including when the target is nonzero. -/
theorem frequencyCoset_card (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) :
    (frequencyCoset Q.mkQ θ).card =
      2 ^ (Module.finrank F2 H * Module.finrank F2 Q) := by
  classical
  rw [frequencyCoset, ← Fintype.card_subtype]
  calc
    Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp (Φ + θ) = 0} =
        Fintype.card {Φ : H →ₗ[F2] E // Q.mkQ.comp Φ = 0} :=
      Fintype.card_congr (Equiv.subtypeEquiv (Equiv.addRight θ) (fun _ => Iff.rfl))
    _ = Fintype.card (H →ₗ[F2] Q) :=
      UniqueGamesTheorem.Fourier.MatrixRestrictions.quotientKernel_card Q
    _ = _ := card_linearMaps

theorem frequencyCoset_card_le (Q : Submodule F2 E) [Fintype (H →ₗ[F2] Q)]
    (θ : H →ₗ[F2] E) (ℓ r : ℕ)
    (hH : Module.finrank F2 H ≤ ℓ) (hQ : Module.finrank F2 Q ≤ r) :
    (frequencyCoset Q.mkQ θ).card ≤ 2 ^ (ℓ * r) := by
  rw [frequencyCoset_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul hH hQ)

end CosetCardinality

section Averaging

variable {SigmaChar : Type*} [Fintype SigmaChar] [Nonempty SigmaChar]

omit [Nonempty SigmaChar] in
/-- Discarding a set of characters costs at most its actual uniform mass. -/
theorem remove_bad_characters (C : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (a b : ℝ) (hC : ∀ σ, |C σ| ≤ 1)
    (hcorrelation : a ≤ 𝔼 σ, |C σ|)
    (hbad : (𝔼 σ, if good σ then (0 : ℝ) else 1) ≤ b) :
    a - b ≤ 𝔼 σ, if good σ then |C σ| else 0 := by
  classical
  have hp : (𝔼 σ, |C σ|) ≤
      (𝔼 σ, if good σ then |C σ| else 0) +
      (𝔼 σ, if good σ then (0 : ℝ) else 1) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simp [hg]
    · simpa [hg] using hC σ
  linarith

/-- The second Cauchy--Schwarz step in private decoding.  The first step is
`sliceCorrelation_sq_le_coset_mass`; the mass is the actual sampled Fourier
mass and `good` selects nontrivial output characters. -/
theorem average_coset_mass_lower (C mass : SigmaChar → ℝ) (good : SigmaChar → Prop)
    (N c : ℝ) (hN : 0 < N) (hc : 0 ≤ c)
    (hcorrelation : c ≤ 𝔼 σ, if good σ then |C σ| else 0)
    (hpoint : ∀ σ, good σ → C σ ^ 2 ≤ N * mass σ) :
    c ^ 2 / N ≤ 𝔼 σ, if good σ then mass σ else 0 := by
  classical
  let d : SigmaChar → ℝ := fun σ => if good σ then |C σ| else 0
  have hj := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at hj
  have hp : (𝔼 σ, d σ ^ 2) ≤ N * (𝔼 σ, if good σ then mass σ else 0) := by
    rw [Finset.mul_expect]
    apply Finset.expect_le_expect
    intro σ _
    by_cases hg : good σ
    · simpa [d, hg, sq_abs] using hpoint σ hg
    · simp [d, hg]
  have hs : c ^ 2 ≤ (𝔼 σ, d σ) ^ 2 := by
    have hd : c ≤ 𝔼 σ, d σ := hcorrelation
    nlinarith
  apply (div_le_iff₀ hN).2
  nlinarith

end Averaging

section Contraction

variable {E H : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup H] [Module F2 H]

/-- A frequency in the target coset contracts into `z + Q`. -/
theorem contraction_mem_target_coset (Q : Submodule F2 E)
    (σ : H →ₗ[F2] F2) (z : E) (Φ : H →ₗ[F2] E) (h : H)
    (hσ : σ h = 1) (hcoset : Q.mkQ.comp (Φ + σ.smulRight z) = 0) :
    Φ h - z ∈ Q := by
  have hq := LinearMap.congr_fun hcoset h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    hσ, one_smul, LinearMap.zero_apply] at hq
  have hmem : Φ h + z ∈ Q := by
    change Q.mkQ (Φ h + z) = 0 at hq
    exact (Submodule.Quotient.mk_eq_zero Q).mp hq
  have hz : -z = z := by
    have htwo : (1 + 1 : F2) = 0 := by decide
    have hzz : z + z = 0 := by
      have hh := congrArg (fun a : F2 => a • z) htwo
      simpa only [add_smul, one_smul, zero_smul] using hh
    exact neg_eq_iff_add_eq_zero.mpr hzz
  simpa only [sub_eq_add_neg, hz] using hmem

end Contraction

section IndependentSampling

variable {U O Ω : Type*} [Fintype Ω]

/-- If the returned projected answer has a preimage in the candidate set, the
uniform, independently sampled candidate finds a preimage with this probability. -/
theorem uniform_preimage_probability (s : Finset U) (π : U → O) (b : O)
    (preimage : ∃ u ∈ s, π u = b) :
    1 / (s.card : ℝ) ≤ 𝔼 u ∈ s, if π u = b then (1 : ℝ) else 0 := by
  classical
  obtain ⟨u, hu, hπ⟩ := preimage
  have hsum : (1 : ℝ) ≤ ∑ v ∈ s, if π v = b then (1 : ℝ) else 0 := by
    have hnonneg : ∀ v ∈ s, (0 : ℝ) ≤ if π v = b then 1 else 0 := by
      intro v _
      split <;> norm_num
    have h := Finset.single_le_sum hnonneg hu
    simpa only [hπ, ite_true] using h
  rw [Finset.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- An explicit product sampling law: the left strategy samples uniformly from
`s`, independently of the right strategy's private sample.  Only positive-mass
good samples need a preimage; no private Fourier information is passed left. -/
theorem independent_agreement_lower (s : Finset U) (π : U → O)
    (answer : Ω → O) (weight : Ω → ℝ) (good : Ω → Prop)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (preimage : ∀ ω, good ω → 0 < weight ω → ∃ u ∈ s, π u = answer ω) :
    (∑ ω, if good ω then weight ω else 0) / (s.card : ℝ) ≤
      ∑ ω, weight ω * (𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω _
  have havg : 0 ≤ 𝔼 u ∈ s, if π u = answer ω then (1 : ℝ) else 0 :=
    Finset.expect_nonneg fun _ _ => by positivity
  by_cases hg : good ω
  · simp only [hg, ite_true]
    by_cases hw : 0 < weight ω
    · have hb := uniform_preimage_probability s π (answer ω) (preimage ω hg hw)
      have := mul_le_mul_of_nonneg_left hb (hweight ω)
      simpa only [div_eq_mul_inv, one_mul] using this
    · have hz : weight ω = 0 := le_antisymm (le_of_not_gt hw) (hweight ω)
      simp [hz]
  · simp only [hg, ite_false, zero_div]
    exact mul_nonneg (hweight ω) havg

end IndependentSampling

end UniqueGamesTheorem.Decoder.PrivateFourier

end

end

end OAI
