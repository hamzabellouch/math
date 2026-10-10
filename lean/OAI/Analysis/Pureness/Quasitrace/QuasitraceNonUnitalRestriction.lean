import OAI.Analysis.Pureness.Quasitrace.QuasitraceComplex

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule IsMulCommutative
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : PositiveQuasitrace D)

def nonUnitalSubalgebraSelfAdjointMap (S : NonUnitalStarSubalgebra ℂ D) : selfAdjoint S →ₗ[ℝ] selfAdjoint D where
  toFun a := ⟨a.1.1,congrArg Subtype.val a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def nonUnitalSubalgebraRealLinear (S : NonUnitalStarSubalgebra ℂ D) [IsMulCommutative S] : selfAdjoint S →ₗ[ℝ] ℝ where
  toFun a := T.selfAdjointValue (nonUnitalSubalgebraSelfAdjointMap S a)
  map_add' a b := by
    rw [map_add,T.selfAdjointValue_add]
    exact congrArg Subtype.val (mul_comm a.1 b.1)
  map_smul' r a := by
    rw [_root_.map_smul,T.selfAdjointValue_smul]
    rfl

def nonUnitalSubalgebraComplexLinear (S : NonUnitalStarSubalgebra ℂ D) [IsMulCommutative S] : S →ₗ[ℂ] ℂ where
  toFun x := (T.nonUnitalSubalgebraRealLinear S (ℜ x) : ℂ)+Complex.I*(T.nonUnitalSubalgebraRealLinear S (ℑ x) : ℂ)
  map_add' x y := by simp only [map_add,Complex.ofReal_add]; ring
  map_smul' z x := by
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,_root_.map_smul,
      RingHom.id_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul]
    apply Complex.ext <;> simp

lemma nonUnitalSubalgebraComplexLinear_eq (S : NonUnitalStarSubalgebra ℂ D) [IsMulCommutative S] (x : S) :
    T.nonUnitalSubalgebraComplexLinear S x = T.complexValue x.1 := by
  rfl
end CuntzPureness.PositiveQuasitrace

end

end OAI
