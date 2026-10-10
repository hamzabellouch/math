import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupCStarAlgebra
import OAI.Analysis.Pureness.Traces.TracialStates
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI
noncomputable section
namespace CuntzPureness
local instance reducedGroupTraceDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open scoped lp InnerProductSpace ComplexOrder
variable (G : Type*) [Group G]

instance (priority := 2000) reducedGroupPartialOrder : PartialOrder (reducedGroupAlgebra G) :=
  CStarAlgebra.spectralOrder _
instance (priority := 2000) reducedGroupPreorder : Preorder (reducedGroupAlgebra G) :=
  (reducedGroupPartialOrder G).toPreorder
instance (priority := 2000) reducedGroupLE : LE (reducedGroupAlgebra G) :=
  (reducedGroupPartialOrder G).toLE
instance reducedGroupStarOrderedRing : StarOrderedRing (reducedGroupAlgebra G) :=
  CStarAlgebra.spectralOrderedRing _
instance (priority := 2000) reducedGroupOrderedAdd : IsOrderedAddMonoid (reducedGroupAlgebra G) :=
  StarOrderedRing.toIsOrderedAddMonoid

def groupVacuumFunctional : GroupOperator G →L[ℂ] ℂ where
  toFun T := ⟪groupVacuum, T groupVacuum⟫_ℂ
  map_add' T S := by simp
  map_smul' c T := by simp
  cont := continuous_const.inner (continuous_id.clm_apply continuous_const)

lemma groupVacuumFunctional_apply (T : GroupOperator G) :
    groupVacuumFunctional G T = (T groupVacuum) 1 := groupVacuum_inner _

lemma groupVacuumFunctional_square (T : GroupOperator G) :
    groupVacuumFunctional G (star T*T) = (‖T groupVacuum‖^2 : ℝ) := by
  change ⟪groupVacuum, (ContinuousLinearMap.adjoint T) (T groupVacuum)⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma groupVacuumFunctional_one : groupVacuumFunctional G 1 = 1 := by
  change ⟪groupVacuum (G := G), groupVacuum⟫_ℂ = 1
  simp [inner_self_eq_norm_sq_to_K, groupVacuum_norm]

lemma groupVacuumFunctional_generator (g : G) :
    groupVacuumFunctional G (groupLeft g) = if g=1 then 1 else 0 := by
  classical
  rw [groupVacuumFunctional_apply, groupLeft_vacuum]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

lemma groupVacuumFunctional_generator_cycle (g : G) (a : reducedGroupAlgebra G) :
    groupVacuumFunctional G (groupLeft g * (a : GroupOperator G)) =
      groupVacuumFunctional G ((a : GroupOperator G) * groupLeft g) := by
  have hv : groupLeft g groupVacuum = groupRight g⁻¹ groupVacuum := by
    classical
    simp [groupLeft_vacuum, groupRight_vacuum]
  simp only [groupVacuumFunctional_apply, mul_apply_eq_comp]
  rw [hv]
  have hc := congrArg (fun T : GroupOperator G => T groupVacuum)
    (reducedGroup_commute_right G a g⁻¹).eq
  change (groupLeft g ((a : GroupOperator G) groupVacuum)) 1 = _
  rw [show (a : GroupOperator G) (groupRight g⁻¹ groupVacuum) =
    groupRight g⁻¹ ((a : GroupOperator G) groupVacuum) from hc]
  simp

theorem groupVacuumFunctional_tracial (a b : reducedGroupAlgebra G) :
    groupVacuumFunctional G ((a : GroupOperator G)*b) =
      groupVacuumFunctional G ((b : GroupOperator G)*a) := by
  have hc : IsClosed {x : GroupOperator G | groupVacuumFunctional G (x*b) =
      groupVacuumFunctional G ((b : GroupOperator G)*x)} :=
    isClosed_eq ((groupVacuumFunctional G).continuous.comp (continuous_id.mul continuous_const))
      ((groupVacuumFunctional G).continuous.comp (continuous_const.mul continuous_id))
  apply closure_minimal (t := {x : GroupOperator G | groupVacuumFunctional G (x*b) =
    groupVacuumFunctional G ((b : GroupOperator G)*x)}) ?_ hc a.property
  intro x hx
  change x ∈ Submodule.span ℂ (Set.range (groupLeft (G := G))) at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨g,rfl⟩ := hx; exact groupVacuumFunctional_generator_cycle G g b
  | zero => simp
  | add x y _ _ hx hy => simp_all [add_mul, mul_add]
  | smul c x _ hx => simpa [smul_mul_assoc, mul_smul_comm] using congrArg (c • ·) hx

lemma groupVacuumFunctional_nonneg (a : reducedGroupAlgebra G) (ha : 0 ≤ a) :
    0 ≤ groupVacuumFunctional G a := by
  have he : a = star (CFC.sqrt a)*CFC.sqrt a := by
    rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
  change 0 ≤ groupVacuumFunctional G (a : GroupOperator G)
  rw [he]
  change 0 ≤ groupVacuumFunctional G
    (star ((CFC.sqrt a : reducedGroupAlgebra G) : GroupOperator G)*
      ((CFC.sqrt a : reducedGroupAlgebra G) : GroupOperator G))
  rw [groupVacuumFunctional_square]
  exact_mod_cast sq_nonneg ‖((CFC.sqrt a : reducedGroupAlgebra G) : GroupOperator G) groupVacuum‖

def reducedGroupTracialState : TracialState (reducedGroupAlgebra G) where
  functional :=
    { toLinearMap := (groupVacuumFunctional G).toLinearMap.comp
        (reducedGroupAlgebra G).subtype.toLinearMap
      monotone' := by
        intro a b hab
        apply sub_nonneg.mp
        change 0 ≤ groupVacuumFunctional G (b : GroupOperator G) -
          groupVacuumFunctional G (a : GroupOperator G)
        rw [← map_sub]
        exact groupVacuumFunctional_nonneg G (b-a) (sub_nonneg.mpr hab) }
  normalized := groupVacuumFunctional_one G
  tracial := groupVacuumFunctional_tracial G

lemma reducedGroupTracialState_apply (a : reducedGroupAlgebra G) :
    (reducedGroupTracialState G).functional a = groupVacuumFunctional G a := rfl

theorem reducedGroupTracialState_faithful (a : reducedGroupAlgebra G) :
    (reducedGroupTracialState G).functional (star a*a)=0 ↔ a=0 := by
  rw [reducedGroupTracialState_apply]
  change groupVacuumFunctional G (star (a : GroupOperator G)*a)=0 ↔ a=0
  rw [groupVacuumFunctional_square]
  constructor
  · intro h
    have hn : ‖(a : GroupOperator G) groupVacuum‖^2 = 0 := by exact_mod_cast h
    exact reducedGroup_vacuum_separating G a (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro h
    simp [h]
end CuntzPureness

end

end OAI
