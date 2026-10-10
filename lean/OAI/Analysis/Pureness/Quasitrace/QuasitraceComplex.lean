import OAI.Analysis.Pureness.Quasitrace.QuasitraceSelfAdjoint

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule IsMulCommutative
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
namespace PositiveQuasitrace
variable (T : PositiveQuasitrace D)

def complexValue (x : D) : ℂ :=
  (T.selfAdjointValue (ℜ x) : ℂ) + Complex.I*(T.selfAdjointValue (ℑ x) : ℂ)

lemma complexValue_selfAdjoint (a : selfAdjoint D) :
    T.complexValue a.1 = (T.selfAdjointValue a : ℂ) := by
  have hr : ℜ a.1 = a := Subtype.ext a.2.coe_realPart
  simp only [complexValue,hr,a.2.imaginaryPart,T.selfAdjointValue_zero,Complex.ofReal_zero,mul_zero,add_zero]

lemma complexValue_positive (a : Positive D) : T.complexValue a.1 = (T a : ℂ) := by
  rw [T.complexValue_selfAdjoint ⟨a.1,a.2.isSelfAdjoint⟩,T.selfAdjointValue_positive]

lemma complexValue_polar (x : D) : T.complexValue (star x*x) = T.complexValue (x*star x) := by
  exact (T.complexValue_positive (Positive.starMul x)).trans
    ((congrArg Complex.ofReal (T.polar x)).trans (T.complexValue_positive (Positive.mulStar x)).symm)

lemma complexValue_square_nonneg (x : D) : 0 ≤ T.complexValue (star x*x) := by
  change 0 ≤ T.complexValue (Positive.starMul x).1
  rw [T.complexValue_positive]
  exact_mod_cast T.nonneg (Positive.starMul x)

lemma complexValue_real_add_I (a b : selfAdjoint D) :
    T.complexValue (a.1+Complex.I • b.1) = T.complexValue a.1+Complex.I*T.complexValue b.1 := by
  rw [T.complexValue_selfAdjoint a,T.complexValue_selfAdjoint b]
  unfold complexValue
  have hr : ℜ (a.1+Complex.I • b.1) = a := by
    apply Subtype.ext
    simp [_root_.map_add,realPart_smul,b.2.imaginaryPart]
  have hi : ℑ (a.1+Complex.I • b.1) = b := by
    apply Subtype.ext
    simp [_root_.map_add,imaginaryPart_smul,a.2.imaginaryPart,b.2.imaginaryPart]
  rw [hr,hi]

def subalgebraSelfAdjointMap (S : StarSubalgebra ℂ D) : selfAdjoint S →ₗ[ℝ] selfAdjoint D where
  toFun a := ⟨a.1.1,congrArg Subtype.val a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def subalgebraRealLinear (S : StarSubalgebra ℂ D) [IsMulCommutative S] : selfAdjoint S →ₗ[ℝ] ℝ where
  toFun a := T.selfAdjointValue (subalgebraSelfAdjointMap S a)
  map_add' a b := by
    rw [map_add,T.selfAdjointValue_add]
    exact congrArg Subtype.val (mul_comm a.1 b.1)
  map_smul' r a := by
    rw [_root_.map_smul,T.selfAdjointValue_smul]
    rfl

def subalgebraComplexLinear (S : StarSubalgebra ℂ D) [IsMulCommutative S] : S →ₗ[ℂ] ℂ where
  toFun x := (T.subalgebraRealLinear S (ℜ x) : ℂ)+Complex.I*(T.subalgebraRealLinear S (ℑ x) : ℂ)
  map_add' x y := by simp only [map_add,Complex.ofReal_add]; ring
  map_smul' z x := by
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,_root_.map_smul,
      RingHom.id_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul]
    apply Complex.ext <;> simp

lemma subalgebraComplexLinear_eq (S : StarSubalgebra ℂ D) [IsMulCommutative S] (x : S) :
    T.subalgebraComplexLinear S x = T.complexValue x.1 := by
  rfl
end PositiveQuasitrace
end CuntzPureness

end

end OAI
