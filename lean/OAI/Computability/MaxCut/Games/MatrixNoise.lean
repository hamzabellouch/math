import Mathlib
import OAI.Computability.MaxCut.PCP.MatrixParity
import OAI.Computability.MaxCut.Games.MatrixFourier

namespace OAI

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MaxCutGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open MaxCutGames.Integration.BinaryLinear (Vector)
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

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
    _ = _ := by unfold linearCoeff; ring

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

end MaxCutGames.Fourier.MatrixNoise
end

end OAI
