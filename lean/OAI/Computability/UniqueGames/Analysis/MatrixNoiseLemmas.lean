import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Analysis.AntecedentCountLemmas
import OAI.Computability.UniqueGames.Analysis.DegreeCover
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas

namespace OAI

section

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UniqueGamesTheorem.Fourier.MatrixNoise

open scoped BigOperators Matrix
open UniqueGamesTheorem.Integration.BinaryLinear (Vector)
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

section Additive

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H]

/-- Uniform subgroup averaging is diagonal on every additive character. -/
theorem character_average_shift (ψ : AddChar G ℂ) (A : H →+ G) (x : G) :
    (𝔼 h, ψ (x + A h)) =
      (if ψ.compAddMonoidHom A = 0 then (1 : ℂ) else 0) * ψ x := by
  classical
  have havg : (𝔼 h, (ψ.compAddMonoidHom A) h) =
      if ψ.compAddMonoidHom A = 0 then (1 : ℂ) else 0 := by
    rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
    split_ifs <;> simp
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.mul_expect]
  change ψ x * (𝔼 h, (ψ.compAddMonoidHom A) h) = _
  rw [havg, mul_comm]

end Additive

/-- The additive character obtained by pairing against a binary vector. -/
def dotCharacter {m : Nat} (w : Vector m) : AddChar (Vector m) ℂ where
  toFun ℓ := binarySign (ℓ ⬝ᵥ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [add_dotProduct, binarySign_add]

@[simp] theorem dotCharacter_apply {m : Nat} (w ℓ : Vector m) :
    dotCharacter w ℓ = binarySign (ℓ ⬝ᵥ w) := rfl

theorem dotCharacter_eq_zero_iff {m : Nat} (w : Vector m) :
    dotCharacter w = 0 ↔ w = 0 := by
  classical
  constructor
  · intro h
    funext i
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (Vector m) ℂ => ψ (Pi.single i 1)) h
    simpa [dotCharacter, single_one_dotProduct] using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_dotCharacter {m : Nat} (w : Vector m) :
    (𝔼 ℓ, binarySign (ℓ ⬝ᵥ w)) = if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, dotCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [dotCharacter_eq_zero_iff]
  split_ifs <;> simp

/-- Uniform linear functionals detect precisely whether `S v` vanishes. -/
theorem average_rankOne_character {m n : Nat}
    (S : Matrix (Fin m) (Fin n) F2) (v : Vector n) :
    (𝔼 ℓ : Vector m, traceCharacter S (Matrix.vecMulVec v ℓ)) =
      if S *ᵥ v = 0 then (1 : ℂ) else 0 := by
  simp only [traceCharacter_apply, tracePair, MatrixParity.trace_rankOne]
  exact average_dotCharacter _

def noiseOperator {m n : Nat} (weight : Vector n → ℝ)
    (f : Matrix (Fin n) (Fin m) F2 → ℂ)
    (X : Matrix (Fin n) (Fin m) F2) : ℂ :=
  ∑ v, (weight v : ℂ) * (𝔼 ℓ : Vector m, f (X + Matrix.vecMulVec v ℓ))

/-- The probability of the event `S v = 0`, with the supplied finite weights. -/
def noiseEigenvalue {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) : ℝ :=
  ∑ v, weight v * if S *ᵥ v = 0 then 1 else 0

/-- Equation (5.3), for the actual finite binary matrix operator. -/
theorem noiseOperator_character {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) (X : Matrix (Fin n) (Fin m) F2) :
    noiseOperator weight (traceCharacter S) X =
      (noiseEigenvalue weight S : ℂ) * traceCharacter S X := by
  classical
  unfold noiseOperator noiseEigenvalue
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_expect, average_rankOne_character]
  change _ = Complex.ofRealHom (∑ v, weight v * if S *ᵥ v = 0 then 1 else 0) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp [mul_comm]

theorem noiseEigenvalue_nonneg {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) (hw : ∀ v, 0 ≤ weight v) :
    0 ≤ noiseEigenvalue weight S := by
  unfold noiseEigenvalue
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hw]

theorem noiseEigenvalue_le_one {m n : Nat} (weight : Vector n → ℝ)
    (S : Matrix (Fin m) (Fin n) F2) (hw : ∀ v, 0 ≤ weight v)
    (hnorm : ∑ v, weight v = 1) : noiseEigenvalue weight S ≤ 1 := by
  unfold noiseEigenvalue
  calc
    (∑ v, weight v * if S *ᵥ v = 0 then 1 else 0) ≤ ∑ v, weight v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp [hw]
    _ = 1 := hnorm

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- Evaluation of a uniformly chosen linear functional is a binary character. -/
def evaluationCharacter (w : E) : AddChar (E →ₗ[F2] F2) ℂ where
  toFun ℓ := binarySign (ℓ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp only [LinearMap.add_apply, binarySign_add]

@[simp] theorem evaluationCharacter_apply (w : E) (ℓ : E →ₗ[F2] F2) :
    evaluationCharacter w ℓ = binarySign (ℓ w) := rfl

theorem evaluationCharacter_eq_zero_iff (w : E) :
    evaluationCharacter w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F2 w).mp
    intro ℓ
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (E →ₗ[F2] F2) ℂ => ψ ℓ) h
    simpa using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_evaluationCharacter [Fintype (E →ₗ[F2] F2)] (w : E) :
    (𝔼 ℓ : E →ₗ[F2] F2, binarySign (ℓ w)) =
      if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, evaluationCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [evaluationCharacter_eq_zero_iff]
  split_ifs <;> simp

/-- Basis-independent uniform-functional cancellation in Lemma 5.1. -/
theorem average_smulRight_character [FiniteDimensional F2 F]
    [Fintype (E →ₗ[F2] F2)] (S : F →ₗ[F2] E) (v : F) :
    (𝔼 ℓ : E →ₗ[F2] F2, linearTraceCharacter S (ℓ.smulRight v)) =
      if S v = 0 then (1 : ℂ) else 0 := by
  simp only [linearTraceCharacter_apply, linearTracePair,
    MatrixParity.trace_smulRight_comp]
  exact average_evaluationCharacter _

def linearNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) : ℂ :=
  ∑ v, (weight v : ℂ) * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

theorem linearNoiseOperator_sum [Fintype F] [Fintype (E →ₗ[F2] F2)]
    {I : Type*} [Fintype I] (weight : F → ℝ)
    (f : I → (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (fun Y => ∑ i, f i Y) X =
      ∑ i, linearNoiseOperator weight (f i) X := by
  unfold linearNoiseOperator
  simp_rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_comm

theorem linearNoiseOperator_smul [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (c : ℂ) (f : (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (fun Y => c * f Y) X =
      c * linearNoiseOperator weight f X := by
  unfold linearNoiseOperator
  simp_rw [← Finset.mul_expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

/-- Weighted probability that the dual map annihilates the sampled noise vector. -/
def linearNoiseEigenvalue [Fintype F] (weight : F → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ v, weight v * if S v = 0 then 1 else 0

/-- Equation (5.3), without a choice of bases. -/
theorem linearNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (linearTraceCharacter S) X =
      (linearNoiseEigenvalue weight S : ℂ) * linearTraceCharacter S X := by
  classical
  unfold linearNoiseOperator linearNoiseEigenvalue
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_expect, average_smulRight_character]
  change _ = Complex.ofRealHom (∑ v, weight v * if S v = 0 then 1 else 0) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp [mul_comm]

theorem linearNoiseEigenvalue_nonneg [Fintype F] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (hw : ∀ v, 0 ≤ weight v) :
    0 ≤ linearNoiseEigenvalue weight S := by
  unfold linearNoiseEigenvalue
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hw]

theorem linearNoiseEigenvalue_le_one [Fintype F] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (hw : ∀ v, 0 ≤ weight v)
    (hnorm : ∑ v, weight v = 1) : linearNoiseEigenvalue weight S ≤ 1 := by
  unfold linearNoiseEigenvalue
  calc
    (∑ v, weight v * if S v = 0 then 1 else 0) ≤ ∑ v, weight v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp [hw]
    _ = 1 := hnorm

def linearRealNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ v, weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

theorem linearRealNoiseOperator_complex [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    (linearRealNoiseOperator weight f X : ℂ) =
      linearNoiseOperator weight (fun Y => (f Y : ℂ)) X := by
  unfold linearRealNoiseOperator linearNoiseOperator
  change Complex.ofRealHom (∑ v, weight v * _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  change ((weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, complex_ofReal_expect]

theorem linearRealNoiseOperator_eq_re [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight f X =
      (linearNoiseOperator weight (fun Y => (f Y : ℂ)) X).re := by
  rw [← linearRealNoiseOperator_complex]
  rfl

theorem linearRealNoiseOperator_sum [Fintype F] [Fintype (E →ₗ[F2] F2)]
    {I : Type*} [Fintype I] (weight : F → ℝ)
    (f : I → (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => ∑ i, f i Y) X =
      ∑ i, linearRealNoiseOperator weight (f i) X := by
  unfold linearRealNoiseOperator
  simp_rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_comm

theorem linearRealNoiseOperator_smul [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => c * f Y) X =
      c * linearRealNoiseOperator weight f X := by
  unfold linearRealNoiseOperator
  simp_rw [← Finset.mul_expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

theorem linearRealNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => (linearTraceCharacter S Y).re) X =
      linearNoiseEigenvalue weight S * (linearTraceCharacter S X).re := by
  apply Complex.ofReal_injective
  rw [linearRealNoiseOperator_complex]
  simpa only [Complex.ofReal_mul, linearTraceCharacter_real] using
    (linearNoiseOperator_character weight S X)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier expansion of the actual noise operator on every real function. -/
theorem linearRealNoiseOperator_expansion (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight f X =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S *
        (linearTraceCharacter S X).re := by
  classical
  calc
    linearRealNoiseOperator weight f X = linearRealNoiseOperator weight
        (fun Y => ∑ S : F →ₗ[F2] E,
          linearCoeff f S * (linearTraceCharacter S Y).re) X := by
      congr 1
      funext Y
      exact (linear_fourier_inversion f Y).symm
    _ = ∑ S : F →ₗ[F2] E,
        linearCoeff f S * linearRealNoiseOperator weight
          (fun Y => (linearTraceCharacter S Y).re) X := by
      rw [linearRealNoiseOperator_sum]
      simp_rw [linearRealNoiseOperator_smul]
    _ = _ := by
      simp_rw [linearRealNoiseOperator_character]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl

/-- Exact spectral pairing identity for the actual operator. -/
theorem linearRealNoiseOperator_pairing (weight : F → ℝ)
    (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight g X) =
      ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S := by
  simp_rw [linearRealNoiseOperator_expansion, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    (𝔼 X, f X * (linearNoiseEigenvalue weight S * linearCoeff g S *
        (linearTraceCharacter S X).re)) =
        linearNoiseEigenvalue weight S * linearCoeff g S *
          (𝔼 X, f X * (linearTraceCharacter S X).re) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro X _
      ac_rfl
    _ = _ := mul_right_comm _ _ _

/-- The actual real operator is self-adjoint under uniform measure. -/
theorem linearRealNoiseOperator_selfAdjoint (weight : F → ℝ)
    (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight g X) =
      𝔼 X, linearRealNoiseOperator weight f X * g X := by
  calc
    _ = ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S :=
      linearRealNoiseOperator_pairing weight f g
    _ = ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff g S * linearCoeff f S := by
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = 𝔼 X, g X * linearRealNoiseOperator weight f X :=
      (linearRealNoiseOperator_pairing weight g f).symm
    _ = _ := by
      apply Finset.expect_congr rfl
      intro X _
      exact mul_comm _ _

/-- The actual noise operator multiplies each Fourier coefficient by its
annihilation probability. Uniform outer weights specialize to the kernel-rank
multiplier used in Appendix A. -/
theorem linearRealNoiseOperator_coeff (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (linearRealNoiseOperator weight f) S =
      linearNoiseEigenvalue weight S * linearCoeff f S := by
  classical
  change (𝔼 X, linearRealNoiseOperator weight f X *
    (linearTraceCharacter S X).re) = _
  calc
    (𝔼 X, linearRealNoiseOperator weight f X * (linearTraceCharacter S X).re) =
        𝔼 X, (linearTraceCharacter S X).re * linearRealNoiseOperator weight f X := by
      apply Finset.expect_congr rfl
      intro X _
      exact mul_comm _ _
    _ = ∑ T : F →ₗ[F2] E, linearNoiseEigenvalue weight T *
        linearCoeff (fun X => (linearTraceCharacter S X).re) T * linearCoeff f T :=
      linearRealNoiseOperator_pairing weight _ f
    _ = _ := by
      simp only [linearCoeff_character]
      simp [mul_ite, ite_mul]

/-- The actual operator's quadratic form is precisely its weighted Fourier mass. -/
theorem linearRealNoiseOperator_energy (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight f X) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  rw [linearRealNoiseOperator_pairing]
  simp only [pow_two, mul_assoc]

/-- Nonnegative weights make the actual noise operator positive semidefinite. -/
theorem linearRealNoiseOperator_nonneg (weight : F → ℝ) (hw : ∀ v, 0 ≤ weight v)
    (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ 𝔼 X, f X * linearRealNoiseOperator weight f X := by
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (linearNoiseEigenvalue_nonneg weight S hw) (sq_nonneg _)

/-- The actual two-side inequality used to select one labeling in §5.1. -/
theorem linearRealNoiseOperator_cross_le (weight : F → ℝ) (hw : ∀ v, 0 ≤ weight v)
    (f g : (E →ₗ[F2] F) → ℝ) :
    2 * (𝔼 X, f X * linearRealNoiseOperator weight g X) ≤
      (𝔼 X, f X * linearRealNoiseOperator weight f X) +
        (𝔼 X, g X * linearRealNoiseOperator weight g X) := by
  rw [linearRealNoiseOperator_pairing weight f g,
    linearRealNoiseOperator_energy weight f, linearRealNoiseOperator_energy weight g,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  calc
    2 * (linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S) =
        linearNoiseEigenvalue weight S * (2 * linearCoeff f S * linearCoeff g S) := by
      ac_rfl
    _ ≤ linearNoiseEigenvalue weight S * (linearCoeff f S ^ 2 + linearCoeff g S ^ 2) :=
      mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _)
        (linearNoiseEigenvalue_nonneg weight S hw)
    _ = _ := mul_add _ _ _

/-- The complex implementation agrees with the real spectral energy identity. -/
theorem linearNoiseOperator_energy_re (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * (linearNoiseOperator weight (fun Y => (f Y : ℂ)) X).re) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  simp_rw [← linearRealNoiseOperator_eq_re]
  exact linearRealNoiseOperator_energy weight f

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

end

end

section

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Multiplication of the real binary trace characters. -/
theorem linearTraceCharacter_re_add (S T : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    (linearTraceCharacter (S + T) X).re =
      (linearTraceCharacter S X).re * (linearTraceCharacter T X).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply]
  rw [← linearTraceCharacter_real S X, ← linearTraceCharacter_real T X]
  simp

variable [Fintype (E →ₗ[F2] F)]

/-- Multiplication by a trace character translates frequency. -/
theorem linearCoeff_mul_character (f : (E →ₗ[F2] F) → ℝ)
    (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * (linearTraceCharacter T X).re) S =
      linearCoeff f (S + T) := by
  simp only [linearCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [linearTraceCharacter_re_add]
  ac_rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

/-- Products transform to counting-measure convolution of normalized coefficients. -/
theorem linearCoeff_mul (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * g X) S =
      ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T) := by
  have hexpand : (fun X : E →ₗ[F2] F => f X * g X) =
      ∑ T : F →ₗ[F2] E, linearCoeff f T •
        (fun X => g X * (linearTraceCharacter T X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      f X * g X =
          (∑ T : F →ₗ[F2] E, linearCoeff f T * (linearTraceCharacter T X).re) * g X := by
        rw [linear_fourier_inversion]
      _ = ∑ T : F →ₗ[F2] E,
          linearCoeff f T * (g X * (linearTraceCharacter T X).re) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        ac_rfl
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_mul_character]

/-- Frequency convolution, with counting measure on the frequency space. -/
def coefficientConvolution (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T)

/-- The actual fourth moment equals the squared coefficient-convolution mass. -/
theorem expect_fourth_eq_sum_convolution_sq (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X ^ 4) =
      ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
  calc
    (𝔼 X, f X ^ 4) = 𝔼 X, (f X * f X) ^ 2 := by
      apply Finset.expect_congr rfl
      intro X _
      rw [← pow_two, ← pow_mul]
    _ = ∑ S : F →ₗ[F2] E, linearCoeff (fun X => f X * f X) S ^ 2 :=
      (linear_parseval (fun X => f X * f X)).symm
    _ = ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
      simp only [linearCoeff_mul, coefficientConvolution]

end UniqueGamesTheorem.Fourier.MatrixProducts

end

end

section

/-! The actual F1 witness bound in Lemma A.1. Coefficients remain signed;
absolute values occur only in the majorant. The two predecessor counts and
Cauchy–Schwarz give the factor `2^(6*d^2)`. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.F1Energy
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

def rank (Y : G) : ℕ := Module.finrank F2 Y.range

def Good (X Y : G) : Prop :=
  ∃ R : G, RankBelow R X ∧ RankBelow R Y ∧ RankBelow (X + R) (X + Y)

abbrev BoundedSplit (d : ℕ) (X : G) :=
  {R : G // RankBelow R X ∧ rank R ≤ d ∧ rank (X + R) ≤ d}

theorem add_self_cancel (X R : G) : (X + R) + R = X := by
  rw [add_assoc, DegreeCover.binary_add_self, add_zero]

def translate (R : G) : G ≃ G where
  toFun X := X + R
  invFun X := X + R
  left_inv X := add_self_cancel X R
  right_inv X := add_self_cancel X R

theorem rank_le_of_rankBelow {R Y : G} (h : RankBelow R Y) : rank R ≤ rank Y := by
  change rank Y = rank R + rank (Y - R) at h
  omega

theorem boundedSplit_rank (d : ℕ) (X : G) (R : BoundedSplit d X) : rank X ≤ 2*d := by
  have h := R.property.1
  change rank X = rank R.val + rank (X - R.val) at h
  simp only [sub_eq_add_neg, DegreeCover.binary_neg] at h
  have hR := R.property.2.1
  have hS := R.property.2.2
  omega

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- The checked geometric cover supplies exactly the F1 witness condition. -/
theorem good_of_trivial_intersections (X Y : G)
    (hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥)
    (hk : X.ker ⊔ Y.ker ⊔ (X+Y).ker = ⊤) : Good X Y := by
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  obtain ⟨R,S,C,hX,hY,hZ,hrX,hrY,hrZ⟩ :=
    DegreeCover.outside_bad_rank_cover Y (X+Y)
      (by simpa only [hc] using hi) (by simpa only [hc] using hk)
  have hXS : X = R+S := hc.symm.trans hX
  have hXR : X-R = S := by rw [hXS]; abel
  have hYR : Y-R = C := by rw [hY]; abel
  have hZS : (X+Y)-S = C := by rw [hZ]; abel
  have hSR : X+R = S := by simpa only [sub_eq_add_neg, DegreeCover.binary_neg] using hXR
  change rank (Y+(X+Y)) = rank R + rank S at hrX
  rw [hc] at hrX
  change rank Y = rank R + rank C at hrY
  change rank (X+Y) = rank S + rank C at hrZ
  refine ⟨R, ?_, ?_, ?_⟩
  · change rank X = rank R + rank (X-R)
    rw [hXR]
    exact hrX
  · change rank Y = rank R + rank (Y-R)
    rw [hYR]
    exact hrY
  · rw [hSR]
    change rank (X+Y) = rank S + rank ((X+Y)-S)
    rw [hZS]
    exact hrZ

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem sum_translate (R : G) (f : G → ℝ) :
    (∑ X, f (X+R)) = ∑ X, f X := Equiv.sum_comp (translate R) f

omit [FiniteDimensional F2 F] in
theorem card_bounded_splits_le (d : ℕ) (X : G) :
    Nat.card (BoundedSplit d X) ≤ 2^(4*d^2) := by
  classical
  by_cases h : Nonempty (BoundedSplit d X)
  · have hr := boundedSplit_rank d X (Classical.choice h)
    let inc : BoundedSplit d X → {R : G // RankBelow R X} :=
      fun R => ⟨R.val, R.property.1⟩
    have hinj : Function.Injective inc := by
      intro R S hRS
      exact Subtype.ext (congrArg (fun T : {R : G // RankBelow R X} => T.val) hRS)
    have hc := Nat.card_le_card_of_injective inc hinj
    have hp := TotalPredecessorCount.card_predecessors_le X
    change Nat.card {R : G // RankBelow R X} ≤ 2^(rank X^2) at hp
    have hs : rank X^2 ≤ 4*d^2 := by nlinarith
    exact hc.trans (hp.trans (Nat.pow_le_pow_right (by decide) hs))
  · have hz : Fintype.card (BoundedSplit d X) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun R => h ⟨R⟩⟩
    simp only [Nat.card_eq_fintype_card, hz, zero_le]

omit [FiniteDimensional F2 F] in
theorem card_predecessors_cast_le (d : ℕ) (Y : G) (hy : rank Y ≤ d) :
    (Fintype.card {R : G // RankBelow R Y} : ℝ) ≤ (2:ℝ)^(d^2) := by
  have h := TotalPredecessorCount.card_predecessors_le Y
  change Nat.card {R : G // RankBelow R Y} ≤ 2^(rank Y^2) at h
  have hs : rank Y^2 ≤ d^2 := by nlinarith
  have hp := h.trans (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.card_eq_fintype_card] at hp
  exact_mod_cast hp

def predecessorCoefficient (a : G → ℝ) (R C : G) : ℝ :=
  if RankBelow R (R+C) then |a (R+C)| else 0

def gram (a : G → ℝ) (R S : G) : ℝ :=
  ∑ C, predecessorCoefficient a R C * predecessorCoefficient a S C

def predecessorEnergy (a : G → ℝ) : ℝ :=
  ∑ R, ∑ C, predecessorCoefficient a R C ^ 2

def goodConvolution (a : G → ℝ) (X : G) : ℝ :=
  ∑ Y, if Good X Y then |a Y| * |a (X+Y)| else 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_nonneg (a : G → ℝ) (R C : G) :
    0 ≤ predecessorCoefficient a R C := by
  unfold predecessorCoefficient
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem gram_nonneg (a : G → ℝ) (R S : G) : 0 ≤ gram a R S :=
  Finset.sum_nonneg (fun C _ => mul_nonneg
    (predecessorCoefficient_nonneg a R C) (predecessorCoefficient_nonneg a S C))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_sq (a : G → ℝ) (R C : G) :
    predecessorCoefficient a R C ^ 2 =
      if RankBelow R (R+C) then a (R+C)^2 else 0 := by
  unfold predecessorCoefficient
  split <;> simp only [sq_abs, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_eq (a : G → ℝ) :
    predecessorEnergy a =
      ∑ Y, (Fintype.card {R : G // RankBelow R Y} : ℝ) * a Y^2 := by
  unfold predecessorEnergy
  calc
    _ = ∑ R, ∑ Y, if RankBelow R Y then a Y^2 else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      simp only [predecessorCoefficient_sq]
      simpa only [add_comm] using
        sum_translate R (fun Y => if RankBelow R Y then a Y^2 else 0)
    _ = ∑ Y, ∑ R, if RankBelow R Y then a Y^2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← F1Gram.sum_subtype_eq (fun R => RankBelow R Y) (fun _ => a Y^2)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_nonneg (a : G → ℝ) : 0 ≤ predecessorEnergy a :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 F] in
theorem predecessor_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    predecessorEnergy a ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by
  rw [predecessor_energy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : rank Y ≤ d
  · exact mul_le_mul_of_nonneg_right (card_predecessors_cast_le d Y hY) (sq_nonneg _)
  · rw [hdegree Y (Nat.lt_of_not_ge hY)]
    simp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_nonneg (a : G → ℝ) (X : G) : 0 ≤ goodConvolution a X := by
  apply Finset.sum_nonneg
  intro Y _
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- Each supported good term has a bounded split witness. Its summand is
counted with shared residual C=Y+R; all other summands are nonnegative. -/
theorem good_term_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X Y : G) :
    (if Good X Y then |a Y| * |a (X+Y)| else 0) ≤
      ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) := by
  have hnonneg : 0 ≤ ∑ R : BoundedSplit d X,
      predecessorCoefficient a R.val (Y+R.val) *
        predecessorCoefficient a (X+R.val) (Y+R.val) :=
    Finset.sum_nonneg (fun R _ => mul_nonneg
      (predecessorCoefficient_nonneg a _ _) (predecessorCoefficient_nonneg a _ _))
  by_cases hg : Good X Y
  · rw [ite_eq_left hg]
    by_cases ha : a Y = 0
    · simpa only [ha, abs_zero, zero_mul] using hnonneg
    by_cases hb : a (X+Y) = 0
    · simpa only [hb, abs_zero, mul_zero] using hnonneg
    have hY : rank Y ≤ d := by
      by_contra hn
      exact ha (hdegree Y (Nat.lt_of_not_ge hn))
    have hZ : rank (X+Y) ≤ d := by
      by_contra hn
      exact hb (hdegree (X+Y) (Nat.lt_of_not_ge hn))
    obtain ⟨R,hRX,hRY,hSZ⟩ := hg
    let r : BoundedSplit d X := ⟨R,hRX,
      (rank_le_of_rankBelow hRY).trans hY, (rank_le_of_rankBelow hSZ).trans hZ⟩
    have h1 : R+(Y+R) = Y := by
      calc
        _ = (Y+R)+R := by abel
        _ = Y := add_self_cancel Y R
    have h2 : (X+R)+(Y+R) = X+Y := by
      calc
        _ = (X+Y)+(R+R) := by abel
        _ = X+Y := by rw [DegreeCover.binary_add_self, add_zero]
    have heq : predecessorCoefficient a r.val (Y+r.val) *
        predecessorCoefficient a (X+r.val) (Y+r.val) = |a Y| * |a (X+Y)| := by
      change predecessorCoefficient a R (Y+R) *
        predecessorCoefficient a (X+R) (Y+R) = _
      simp only [predecessorCoefficient, h1, h2, ite_eq_left hRY, ite_eq_left hSZ]
    rw [← heq]
    exact Finset.single_le_sum (fun (s : BoundedSplit d X) _ => mul_nonneg
      (predecessorCoefficient_nonneg a s.val (Y+s.val))
      (predecessorCoefficient_nonneg a (X+s.val) (Y+s.val)))
      (Finset.mem_univ r)
  · rw [ite_eq_right hg]
    exact hnonneg

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_le_gram (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) := by
  calc
    _ ≤ ∑ Y, ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) :=
      Finset.sum_le_sum (fun Y _ => good_term_le a d hdegree X Y)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R.val (fun C =>
        predecessorCoefficient a R.val C * predecessorCoefficient a (X+R.val) C)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_sq_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ^ 2 ≤ (2:ℝ)^(4*d^2) *
      ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
  have hg := goodConvolution_le_gram a d hdegree X
  have hn := goodConvolution_nonneg a X
  have hs : 0 ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) :=
    Finset.sum_nonneg (fun _ _ => gram_nonneg a _ _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : BoundedSplit d X => (1:ℝ)) (fun R => gram a R.val (X+R.val))
  have hcard : (Fintype.card (BoundedSplit d X) : ℝ) ≤ (2:ℝ)^(4*d^2) := by
    have h := card_bounded_splits_le d X
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (∑ R : BoundedSplit d X, gram a R.val (X+R.val))^2 := by nlinarith
    _ ≤ (Fintype.card (BoundedSplit d X):ℝ) *
        ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by simpa using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem split_gram_energy_le (a : G → ℝ) (d : ℕ) :
    (∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2) ≤
      predecessorEnergy a ^ 2 := by
  calc
    _ ≤ ∑ X, ∑ R : G, gram a R (X+R)^2 := by
      apply Finset.sum_le_sum
      intro X _
      exact F1Gram.sum_comp_le (fun R : BoundedSplit d X => R.val)
        Subtype.val_injective (fun R => gram a R (X+R)^2) (fun _ => sq_nonneg _)
    _ = ∑ R, ∑ S, gram a R S^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R (fun S => gram a R S^2)
    _ ≤ predecessorEnergy a ^ 2 := F1Gram.gram_energy_le (predecessorCoefficient a)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, goodConvolution a X^2) ≤ (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
  have he := predecessor_energy_le a d hdegree
  have hn := predecessor_energy_nonneg a
  have hb : 0 ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by positivity
  calc
    _ ≤ (2:ℝ)^(4*d^2) *
        ∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun X _ => goodConvolution_sq_le a d hdegree X)
    _ ≤ (2:ℝ)^(4*d^2) * predecessorEnergy a^2 :=
      mul_le_mul_of_nonneg_left (split_gram_energy_le a d) (by positivity)
    _ ≤ (2:ℝ)^(4*d^2) * ((2:ℝ)^(d^2) * ∑ Y, a Y^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      omega

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- The complement of any bad event covered by `Good` is bounded without
changing the signs of the coefficients in the bad part. -/
theorem abs_complement_sum_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    |∑ Y, if bad Y then 0 else a Y * a (X+Y)| ≤ goodConvolution a X := by
  calc
    _ ≤ ∑ Y, |if bad Y then 0 else a Y * a (X+Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ goodConvolution a X := by
      apply Finset.sum_le_sum
      intro Y _
      by_cases hb : bad Y
      · simp only [ite_eq_left hb, abs_zero]
        split <;> positivity
      · simp only [ite_eq_right hb, ite_eq_left (hcover Y hb), abs_mul, le_refl]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem convolution_split_square_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 +
      2 * (∑ Y, if bad Y then a Y * a (X+Y) else 0)^2 := by
  let u : ℝ := ∑ Y, if bad Y then 0 else a Y * a (X+Y)
  let v : ℝ := ∑ Y, if bad Y then a Y * a (X+Y) else 0
  have hs : (∑ Y, a Y * a (X+Y)) = u+v := by
    dsimp only [u,v]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hb : bad Y <;> simp only [hb, ite_true, ite_false, add_zero, zero_add]
  have hu : |u| ≤ goodConvolution a X := abs_complement_sum_le a X bad hcover
  have hp := mul_nonneg (sub_nonneg.mpr hu)
    (add_nonneg (goodConvolution_nonneg a X) (abs_nonneg u))
  have hu2 : u^2 ≤ goodConvolution a X^2 := by nlinarith [sq_abs u]
  change (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 + 2*v^2
  rw [hs]
  nlinarith [sq_nonneg (u-v)]

omit [FiniteDimensional F2 F] in
theorem convolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (bad : G → G → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (∑ X, (∑ Y, a Y * a (X+Y))^2) ≤
      2 * ((2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
  calc
    _ ≤ ∑ X, (2 * goodConvolution a X^2 +
        2 * (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2) :=
      Finset.sum_le_sum (fun X _ => convolution_split_square_le a X (bad X) (hcover X))
    _ = 2 * (∑ X, goodConvolution a X^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (goodConvolution_energy_le a d hdegree)
        (show (0:ℝ) ≤ 2 by norm_num)) le_rfl

variable [Fintype (F →ₗ[F2] E)]
open UniqueGamesTheorem.Fourier.MatrixFourier UniqueGamesTheorem.Fourier.MatrixProducts

theorem fourier_goodConvolution_energy_le (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, goodConvolution (linearCoeff f) X^2) ≤
      (2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2 := by
  simpa only [linear_parseval] using goodConvolution_energy_le (linearCoeff f) d hdegree

/-- The actual fourth-moment identity reduced to the remaining signed bad
convolution. Its geometric cover is supplied by `good_of_trivial_intersections`. -/
theorem fourth_moment_le_good_bad (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0)
    (bad : (F →ₗ[F2] E) → (F →ₗ[F2] E) → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (𝔼 X, f X^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2) +
      2 * ∑ X, (∑ Y, if bad X Y then linearCoeff f Y * linearCoeff f (X+Y) else 0)^2 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  unfold coefficientConvolution
  simpa only [linear_parseval] using
    convolution_energy_le (linearCoeff f) d hdegree bad hcover

end UniqueGamesTheorem.Appendix.F1Energy

end

end

end OAI
