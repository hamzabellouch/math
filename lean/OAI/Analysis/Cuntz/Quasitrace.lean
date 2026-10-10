import OAI.Analysis.Cuntz.Measure
import OAI.Analysis.Quasitrace.Compactness
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

noncomputable section

/-! Corner-compatible spectral quasitraces and nonunital abelian complex linearity. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {A : Type*} [CStarAlgebra A]

def spectralCornerHom {n : ℕ} (i : Fin n) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := corner i
  map_zero' := corner_zero i
  map_add' := corner_add i
  map_mul' a b := (corner_mul i a b).symm
  map_smul' := corner_smul i
  map_star' a := (corner_star i a).symm

theorem spectralCorner_posPart {n : ℕ} (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    (corner i a)⁺ = corner i a⁺ := by
  exact ((spectralCornerHom (A := A) i).map_cfcₙ (fun t : ℝ => t⁺) a
    (ha := ha) (hφa := corner_selfAdjoint i ha)).symm

theorem spectralCorner_negPart {n : ℕ} (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    (corner i a)⁻ = corner i a⁻ := by
  exact ((spectralCornerHom (A := A) i).map_cfcₙ (fun t : ℝ => t⁻) a
    (ha := ha) (hφa := corner_selfAdjoint i ha)).symm

theorem spectralCorner_realPart {n : ℕ} (i : Fin n) (a : A) :
    (ℜ (corner i a) : CStarMatrix (Fin n) (Fin n) A) = corner i (ℜ a : A) :=
  (map_realPart (spectralCornerHom (A := A) i) a).symm

theorem spectralCorner_imaginaryPart {n : ℕ} (i : Fin n) (a : A) :
    (ℑ (corner i a) : CStarMatrix (Fin n) (Fin n) A) = corner i (ℑ a : A) :=
  (map_imaginaryPart (spectralCornerHom (A := A) i) a).symm

/-- A single rectangular entry implements equality of spectral values between
any positive corner and its one-by-one matrix. -/
theorem CuntzDimensionState.positiveValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) {a : A} (ha : 0 ≤ a) :
    d.positiveValue (corner i a) (corner_nonneg i ha) =
      d.positiveValue (corner (0 : Fin 1) a) (corner_nonneg _ ha) := by
  let S := CFC.sqrt a
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  let x : Matrix (Fin n) (Fin 1) A := Matrix.single i 0 S
  have hx : x*x.conjTranspose = CStarMatrix.ofMatrix.symm (corner i a) := by
    dsimp only [x]
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
    change Matrix.single i i (S*star S) = Matrix.single i i a
    rw [hS, CFC.sqrt_mul_sqrt_self a ha]
  have hy : x.conjTranspose*x = CStarMatrix.ofMatrix.symm (corner (0 : Fin 1) a) := by
    dsimp only [x]
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
    change Matrix.single 0 0 (star S*S) = Matrix.single 0 0 a
    rw [hS, CFC.sqrt_mul_sqrt_self a ha]
  have hp : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose) := by rw [hx]; exact corner_nonneg i ha
  have hq : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x) := by rw [hy]; exact corner_nonneg _ ha
  simpa only [hx, hy, positiveValue] using d.spectralValue_rectangular_gram x hp hq

theorem CuntzDimensionState.signedValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    d.signedValue (corner i a) = d.signedValue (corner (0 : Fin 1) a) := by
  simp only [signedValue, spectralCorner_posPart i ha, spectralCorner_negPart i ha,
    spectralCorner_posPart (0 : Fin 1) ha, spectralCorner_negPart (0 : Fin 1) ha,
    d.positiveValue_corner i (CFC.posPart_nonneg a), d.positiveValue_corner i (CFC.negPart_nonneg a)]

/-- Whole-algebra corner compatibility for the same stabilized construction. -/
theorem CuntzDimensionState.complexValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) (a : A) :
    d.complexValue (corner i a) = d.complexValue (corner (0 : Fin 1) a) := by
  simp only [complexValue, spectralCorner_realPart, spectralCorner_imaginaryPart,
    d.signedValue_corner i (ℜ a).property, d.signedValue_corner i (ℑ a).property]

theorem spectralCorner_finOne (a : A) :
    corner (0 : Fin 1) a = CStarMatrix.toOneByOne (Fin 1) ℂ A a := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [corner, entry, CStarMatrix.toOneByOne]
  rfl

namespace CuntzDimensionState

/-- The same spectral construction on the original coefficient algebra. -/
def baseValue (d : CuntzDimensionState A) (a : A) : ℂ :=
  d.complexValue (corner (0 : Fin 1) a)

theorem baseValue_square_nonneg (d : CuntzDimensionState A) (x : A) :
    0 ≤ d.baseValue (star x*x) := by
  simpa only [baseValue, ← corner_mul, ← corner_star] using
    d.complexValue_square_nonneg (corner (0 : Fin 1) x)

theorem baseValue_square_swap (d : CuntzDimensionState A) (x : A) :
    d.baseValue (star x*x) = d.baseValue (x*star x) := by
  simpa only [baseValue, ← corner_mul, ← corner_star] using
    d.complexValue_square_swap (corner (0 : Fin 1) x)

theorem baseValue_real_imag (d : CuntzDimensionState A) (h k : A)
    (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    d.baseValue (h+Complex.I • k) = d.baseValue h + Complex.I*d.baseValue k := by
  simpa only [baseValue, corner_add, corner_smul] using d.complexValue_real_imag
    (corner (0 : Fin 1) h) (corner (0 : Fin 1) k)
    (corner_selfAdjoint _ hh) (corner_selfAdjoint _ hk)

theorem baseValue_one (d : CuntzDimensionState A) : d.baseValue (1 : A) = 1 := by
  unfold baseValue
  have hc : corner (0 : Fin 1) (1 : A) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [corner, entry]
  rw [hc, d.complexValue_one]
  norm_num

theorem norm_baseValue_le (d : CuntzDimensionState A) (a : A) :
    ‖d.baseValue a‖ ≤ 2*‖a‖ := by
  have h := d.norm_complexValue_le (corner (0 : Fin 1) a)
  have hn : ‖corner (0 : Fin 1) a‖ = ‖a‖ :=
    NonUnitalStarAlgHom.norm_map (spectralCornerHom (A := A) (0 : Fin 1))
      (fun x y h => congrArg (fun M : CStarMatrix (Fin 1) (Fin 1) A => M 0 0) h) a
  change ‖d.complexValue (corner (0 : Fin 1) a)‖ ≤ 2 * ‖a‖
  simpa only [Nat.cast_one, hn, mul_one] using h

/-- A single compatible base/M2 candidate, built from one dimension state.
Only the abelian linearity constraints are still missing. -/
def spectralCandidate (d : CuntzDimensionState A) : QuasitraceCandidate A :=
  (d.baseValue, d.complexValue)

theorem spectralCandidate_corner (d : CuntzDimensionState A) (a : A) :
    d.spectralCandidate.2 (upperLeft a) = d.spectralCandidate.1 a := by
  change d.complexValue (upperLeft a) = d.baseValue a
  rw [upperLeft_eq_corner]
  exact d.complexValue_corner (0 : Fin 2) a

theorem spectralCandidate_matrix_unit (d : CuntzDimensionState A) :
    d.spectralCandidate.2 1 = 2 := by
  exact_mod_cast d.complexValue_one 2

def oneQuasitraceOfSpectralCandidate (d : CuntzDimensionState A)
    (hlin : ∀ S : NonUnitalStarSubalgebra ℂ A, IsClosed (S : Set A) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x) :
    OneQuasitrace A where
  toFun := d.baseValue
  square_nonneg := d.baseValue_square_nonneg
  square_swap := d.baseValue_square_swap
  real_imag := d.baseValue_real_imag
  abelian_linear := hlin

theorem normalizedTwoQuasitrace_of_spectral_linearity (d : CuntzDimensionState A)
    (hlin : ∀ S : NonUnitalStarSubalgebra ℂ A, IsClosed (S : Set A) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x)
    (hlin2 : ∀ S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) A),
      IsClosed (S : Set (CStarMatrix (Fin 2) (Fin 2) A)) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.complexValue (x : CStarMatrix (Fin 2) (Fin 2) A)) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo := by
  let σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A) := {
    toFun := d.complexValue
    square_nonneg := d.complexValue_square_nonneg
    square_swap := d.complexValue_square_swap
    real_imag := d.complexValue_real_imag
    abelian_linear := hlin2 }
  exact ⟨d.oneQuasitraceOfSpectralCandidate hlin, d.baseValue_one,
    σ, d.spectralCandidate_corner⟩

/-- Gelfand duality transfers the proved integral linearity to any unital
commutative C*-algebra represented in a finite matrix algebra over A. -/
def commutativeValueLinearMap (d : CuntzDimensionState A)
    {B : Type*} [CommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : B →ₗ[ℂ] ℂ := by
  letI := borel (WeakDual.characterSpace ℂ B)
  letI : BorelSpace (WeakDual.characterSpace ℂ B) := ⟨rfl⟩
  let ψ := φ.comp (gelfandStarTransform B).symm.toStarAlgHom
  exact (d.complexValueLinearMap ψ).comp (gelfandStarTransform B).toAlgEquiv.toLinearEquiv.toLinearMap

@[simp] theorem commutativeValueLinearMap_apply (d : CuntzDimensionState A)
    {B : Type*} [CommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (b : B) :
    d.commutativeValueLinearMap φ b = d.complexValue (φ b) := by
  change d.complexValue (φ ((gelfandStarTransform B).symm ((gelfandStarTransform B) b))) = _
  rw [StarAlgEquiv.symm_apply_apply]

def nonunitalCommutativeValueLinearMap (d : CuntzDimensionState A)
    {B : Type*} [NonUnitalCommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : B →ₗ[ℂ] ℂ :=
  (d.commutativeValueLinearMap (Unitization.starLift φ)).comp
    (Unitization.inrHom ℂ ℂ B)

@[simp] theorem nonunitalCommutativeValueLinearMap_apply (d : CuntzDimensionState A)
    {B : Type*} [NonUnitalCommCStarAlgebra B] {n : ℕ}
    (φ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (b : B) :
    d.nonunitalCommutativeValueLinearMap φ b = d.complexValue (φ b) := by
  have he : (Unitization.starLift φ) (b : Unitization ℂ B) = φ b :=
    congrArg (fun ψ : B →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A => ψ b)
      (Equiv.symm_apply_apply Unitization.starLift φ)
  have hc := d.commutativeValueLinearMap_apply (Unitization.starLift φ)
    (b : Unitization ℂ B)
  exact hc.trans (congrArg d.complexValue he)

/-- The exact abelian-linearity axiom for the fixed matrix spectral candidate. -/
theorem complexValue_abelian_linear (d : CuntzDimensionState A) (n : ℕ)
    (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin n) (Fin n) A))
    (hS : IsClosed (S : Set (CStarMatrix (Fin n) (Fin n) A)))
    (hcomm : ∀ x y : S, x*y=y*x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.complexValue (x : CStarMatrix (Fin n) (Fin n) A) := by
  let : IsClosed (S : Set (CStarMatrix (Fin n) (Fin n) A)) := hS
  let : NonUnitalCommCStarAlgebra S := { (inferInstance : NonUnitalCStarAlgebra S) with mul_comm := hcomm }
  exact ⟨d.nonunitalCommutativeValueLinearMap (NonUnitalStarSubalgebraClass.subtype S),
    fun x => d.nonunitalCommutativeValueLinearMap_apply _ x⟩

/-- The same axiom at size one, expressed on the original coefficient algebra. -/
theorem baseValue_abelian_linear (d : CuntzDimensionState A)
    (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hcomm : ∀ x y : S, x*y=y*x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x := by
  let : IsClosed (S : Set A) := hS
  let : NonUnitalCommCStarAlgebra S := { (inferInstance : NonUnitalCStarAlgebra S) with mul_comm := hcomm }
  let φ := (spectralCornerHom (A := A) (0 : Fin 1)).comp (NonUnitalStarSubalgebraClass.subtype S)
  exact ⟨d.nonunitalCommutativeValueLinearMap φ,
    fun x => d.nonunitalCommutativeValueLinearMap_apply φ x⟩

/-- A normalized two-quasitrace from a dimension state, with both original
abelian-linearity premises now discharged for the SAME spectral construction. -/
theorem normalizedTwoQuasitrace_exists (d : CuntzDimensionState A) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo :=
  d.normalizedTwoQuasitrace_of_spectral_linearity d.baseValue_abelian_linear
    (d.complexValue_abelian_linear 2)

end CuntzDimensionState
end Kaplansky

end

end OAI
