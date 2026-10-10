import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexRotationDerivation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealCartanRotations

namespace OAI

/-! # Infinitesimal Cartan rotations on the real Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Conjugation respects the imaginary semisimple part for real parameters. -/
theorem complex_imaginaryOperator_conjugation (h : H) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L
      (ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H) (realCartanInComplex L H h) x) =
    ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (complexificationConjugation L x) := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    rw [ComplexCartan.imaginaryOperator_apply _ _ χ hv,complexificationConjugation_smul,
      ComplexCartan.imaginaryOperator_apply_genWeight _ _ (conjugateCartanWeight L H χ)
        (conjugation_mem_genWeightSpace L H χ hv)]
    congr 1
    simp [conjugateCartanWeight,ComplexCartan.imaginaryPart]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]

/-- The imaginary operator preserves the embedded real form. -/
theorem exists_real_imaginaryOperator (h : H) (x : L) :
    ∃ y : L, ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) (1 ⊗ₜ[ℝ] x) = 1 ⊗ₜ[ℝ] y := by
  apply (complexification_conjugation_fixed_iff L _).mp
  rw [complex_imaginaryOperator_conjugation]
  simp

/-- The real imaginary semisimple operator, obtained from the actual complex
weight spaces by real descent. -/
def realImaginaryOperator (h : H) : L →ₗ[ℝ] L :=
  (complexificationRealPart L).comp
    ((ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h)).restrictScalars ℝ |>.comp
      (complexificationLieHom L).toLinearMap)

@[simp] theorem realImaginaryOperator_complexify (h : H) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h x =
      ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
        (realCartanInComplex L H h) (1 ⊗ₜ[ℝ] x) := by
  obtain ⟨y,hy⟩ := exists_real_imaginaryOperator L H h x
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L
    (ComplexCartan.imaginaryOperator (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) (1 ⊗ₜ[ℝ] x)) = _
  rw [hy,complexificationRealPart_tmul,Complex.one_re,one_smul]

theorem realImaginaryOperator_lie (h : H) (x y : L) :
    realImaginaryOperator L H h ⁅x,y⁆ =
      ⁅realImaginaryOperator L H h x,y⁆ + ⁅x,realImaginaryOperator L H h y⁆ := by
  apply complexificationLieHom_injective L
  simp only [map_add,LieHom.map_lie]
  change (1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h ⁅x,y⁆ =
    ⁅(1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ +
    ⁅(1 : ℂ) ⊗ₜ[ℝ] x,(1 : ℂ) ⊗ₜ[ℝ] realImaginaryOperator L H h y⁆
  rw [realImaginaryOperator_complexify,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify]
  simpa only [LieAlgebra.ExtendScalars.bracket_tmul,one_mul] using
    (ComplexCartan.imaginaryOperator_lie (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y))

/-- The infinitesimal compact action as a real derivation. -/
def realImaginaryDerivation (h : H) : LieDerivation ℝ L L where
  toLinearMap := realImaginaryOperator L H h
  leibniz' x y := by
    rw [realImaginaryOperator_lie,← lie_skew (realImaginaryOperator L H h x) y]
    simp only [sub_eq_add_neg,add_comm]

@[simp] theorem realImaginaryOperator_add (h k : H) (x : L) :
    realImaginaryOperator L H (h+k) x = realImaginaryOperator L H h x +
      realImaginaryOperator L H k x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (_ + _)
  rw [TensorProduct.tmul_add,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify,realImaginaryOperator_complexify,
    realCartanInComplex_add,ComplexCartan.imaginaryOperator_add]

@[simp] theorem realImaginaryOperator_zero (x : L) : realImaginaryOperator L H 0 x = 0 := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (0 : L)
  rw [realImaginaryOperator_complexify,realCartanInComplex_zero,
    ComplexCartan.imaginaryOperator_zero,TensorProduct.tmul_zero]

theorem realImaginaryOperator_cartan (h k : H) : realImaginaryOperator L H h k = 0 := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (0 : L)
  rw [realImaginaryOperator_complexify,TensorProduct.tmul_zero]
  exact ComplexCartan.imaginaryOperator_cartan (complexifiedSubalgebra L H)
    (realCartanInComplex L H h) (realCartanInComplex L H k)

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
/-- The real embedding is linear in the Cartan parameter. -/
theorem realCartanInComplex_real_smul (r : ℝ) (h : H) :
    realCartanInComplex L H (r • h) = r • realCartanInComplex L H h := by
  apply Subtype.ext
  change (1 : ℂ) ⊗ₜ[ℝ] (r • (h : L)) = r • ((1 : ℂ) ⊗ₜ[ℝ] (h : L))
  exact TensorProduct.tmul_smul r 1 (h : L)

theorem realImaginaryOperator_smul (r : ℝ) (h : H) (x : L) :
    realImaginaryOperator L H (r • h) x = r • realImaginaryOperator L H h x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] (r • _)
  rw [TensorProduct.tmul_smul,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify,realCartanInComplex_real_smul]
  exact ComplexCartan.imaginaryOperator_real_smul (complexifiedSubalgebra L H) r
    (realCartanInComplex L H h) ((1 : ℂ) ⊗ₜ[ℝ] x)

theorem realImaginaryOperator_commute (h k : H) (x : L) :
    realImaginaryOperator L H h (realImaginaryOperator L H k x) =
      realImaginaryOperator L H k (realImaginaryOperator L H h x) := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realImaginaryOperator_complexify,realImaginaryOperator_complexify,
    realImaginaryOperator_complexify,realImaginaryOperator_complexify]
  exact ComplexCartan.imaginaryOperator_commute _ _ _ _

/-- The imaginary derivation depends linearly on the real Cartan parameter. -/
def realImaginaryDerivationLinear : H →ₗ[ℝ] LieDerivation ℝ L L where
  toFun := realImaginaryDerivation L H
  map_add' h k := by
    ext x
    exact realImaginaryOperator_add L H h k x
  map_smul' r h := by
    ext x
    exact realImaginaryOperator_smul L H r h x

end PolycyclicRecognition

end

end OAI
