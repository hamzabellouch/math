import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CornerComparison

namespace OAI

/-! Partial representations for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable (G M : Type*) [Group G] [CStarAlgebra M]

structure Rep where
  val : G → M
  mul : ∀ g h, val (g*h)=val g*val h
  inv : ∀ g, val g⁻¹=star (val g)

namespace Rep
variable {G M} [PartialOrder M] [StarOrderedRing M]

instance : CoeFun (Rep G M) (fun _ => G → M) := ⟨Rep.val⟩
def support (v : Rep G M) : M := v 1

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma support_mul (v : Rep G M) (g : G) : v.support*v g=v g := by
  rw [support,←v.mul,one_mul]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mul_support (v : Rep G M) (g : G) : v g*v.support=v g := by
  rw [support,←v.mul,mul_one]
omit [PartialOrder M] [StarOrderedRing M] in
lemma support_projection (v : Rep G M) : IsStarProjection v.support := by
  constructor
  · exact v.support_mul 1
  · simpa only [IsSelfAdjoint,support,inv_one] using (v.inv 1).symm
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma star_mul_self (v : Rep G M) (g : G) : star (v g)*v g=v.support := by
  rw [←v.inv,←v.mul,inv_mul_cancel,support]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mul_star_self (v : Rep G M) (g : G) : v g*star (v g)=v.support := by
  rw [←v.inv,←v.mul,mul_inv_cancel,support]
omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_le (v : Rep G M) (g : G) : ‖v g‖≤1 := by
  have hh := v.support_projection.norm_le
  rw [←v.star_mul_self g,CStarRing.norm_star_mul_self] at hh
  nlinarith [norm_nonneg (v g)]

def zero : Rep G M where
  val _ := 0
  mul _ _ := by simp
  inv _ := by simp

def add (v w : Rep G M) (hvw : v.support*w.support=0) : Rep G M where
  val g := v g+w g
  mul g h := by
    have hfg : w.support*v.support=0 := by
      have hh := congrArg star hvw
      simpa only [star_mul,v.support_projection.isSelfAdjoint.star_eq,
        w.support_projection.isSelfAdjoint.star_eq,star_zero] using hh
    have hvw' : v g*w h=0 := by
      calc
        v g*w h = (v g*v.support)*(w.support*w h) := by rw [v.mul_support,w.support_mul]
        _ = v g*(v.support*w.support)*w h := by simp only [mul_assoc]
        _ = 0 := by rw [hvw,mul_zero,zero_mul]
    have hwv : w g*v h=0 := by
      calc
        w g*v h = (w g*w.support)*(v.support*v h) := by rw [w.mul_support,v.support_mul]
        _ = w g*(w.support*v.support)*v h := by simp only [mul_assoc]
        _ = 0 := by rw [hfg,mul_zero,zero_mul]
    simp only [v.mul,w.mul,add_mul,mul_add,hvw',hwv,zero_add,add_zero]
  inv g := by simp only [v.inv,w.inv,star_add]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma add_apply (v w : Rep G M) (hvw) (g : G) : add v w hvw g=v g+w g := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma add_support (v w : Rep G M) (hvw) : (add v w hvw).support=v.support+w.support := rfl
end Rep
end PopaPatching

end

end OAI
