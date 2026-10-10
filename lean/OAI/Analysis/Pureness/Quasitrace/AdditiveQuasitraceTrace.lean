import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitraceBounds
import OAI.Analysis.Pureness.Operators.SelfCommutatorTrace

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule IsMulCommutative
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace ComplexQuasitrace
variable (T : ComplexQuasitrace A)

omit [PartialOrder A] [StarOrderedRing A] in
lemma map_smul_of_normal (c : ℂ) (x : A) [IsStarNormal x] : T (c • x) = c * T x := by
  let S := StarAlgebra.elemental ℂ x
  let a : S := ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩
  have h := (T.subalgebraLinear S).map_smul c a
  simp only [subalgebraLinear_apply, smul_eq_mul] at h
  exact h

def additiveSelfAdjointLinear (hadd : ∀ x y, T (x + y) = T x + T y) :
    selfAdjoint A →ₗ[ℝ] ℂ where
  toFun a := T a.1
  map_add' a b := hadd a.1 b.1
  map_smul' r a := by
    change T (r • a.1) = r • T a.1
    simpa only [Complex.coe_smul, Complex.real_smul] using T.map_smul_of_normal (r : ℂ) a.1

def additiveLinear (hadd : ∀ x y, T (x + y) = T x + T y) : A →ₗ[ℂ] ℂ where
  toFun x := T.additiveSelfAdjointLinear hadd (ℜ x) + Complex.I * T.additiveSelfAdjointLinear hadd (ℑ x)
  map_add' x y := by simp only [map_add]; ring
  map_smul' c x := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      RingHom.id_apply, smul_eq_mul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]

omit [PartialOrder A] [StarOrderedRing A] in
lemma additiveLinear_apply (hadd : ∀ x y, T (x + y) = T x + T y) (x : A) :
    T.additiveLinear hadd x = T x := by
  exact (T.real_add_I (ℜ x) (ℑ x)).symm.trans
    (congrArg T.toFun (realPart_add_I_smul_imaginaryPart x))

def tracialStateOfAdditive (hT : T 1 = 1)
    (hadd : ∀ x y, T (x + y) = T x + T y) : TracialState A where
  functional := PositiveLinearMap.mk₀ (T.additiveLinear hadd) (by
    intro x hx
    rw [T.additiveLinear_apply]
    exact T.nonneg x hx)
  normalized := (T.additiveLinear_apply hadd 1).trans hT
  tracial := linearMap_tracial_of_star_mul (T.additiveLinear hadd) (by
    intro x
    simp only [T.additiveLinear_apply]
    exact T.polar x)

theorem exists_tracialState_agreeing_iff (hT : T 1 = 1) :
    (∃ τ : TracialState A, ∀ x, τ.functional x = T x) ↔
      (∀ x y, T (x + y) = T x + T y) := by
  constructor
  · rintro ⟨τ, hτ⟩ x y
    rw [← hτ, ← hτ, ← hτ, map_add]
  · intro hadd
    exact ⟨T.tracialStateOfAdditive hT hadd, T.additiveLinear_apply hadd⟩
end ComplexQuasitrace
end CuntzPureness

end

end OAI
