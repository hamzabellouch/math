import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ScheduledYield
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.NativeLaws

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldActiveCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def canonicalSideMass {K : ℕ} (w : Work K) (s : Fin 3) (k : Fin 17) : ℝ :=
  ∑ b : w.Branch, if w.splitShape b s = k.val then (branchLaw w).mass b else 0

theorem placedLaw_priority_sideMass {K : ℕ} (w : PlacedWork K)
    (i : Fin 3) :
    JointPopulationRates.sideMass (placedLaw w).mass (w.physicalOrder i) =
      canonicalSideMass w.1 (w.1.priority i) := by
  funext k
  rw [placedLaw_sideMass]
  simp only [Fin.ext_iff, branchShape, encodePhysicalShape_side,
    PlacedWork.physicalOrder, Equiv.trans_apply, Equiv.symm_apply_apply,
    canonicalSideMass, branchLaw_mass]

theorem canonicalSideMass_stageA {K : ℕ} (h : InitialPositive K) (s : Fin 3) :
    canonicalSideMass (.stageA h) s =
      (stageAMarginalLaw (initialShape h.val) h.property s).mass := by
  funext k
  rw [show (stageAMarginalLaw (initialShape h.val) h.property s).mass k =
      marginal (below (initialShape h.val))
        (fun u => (stageALaw (initialShape h.val) u : ℝ)) s k from
    indexedMarginalLaw_mass _ _ _ _ _ _ k]
  change (∑ b : ASplit h, if (below (initialShape h.val))[b.val] s = k.val
      then (stageALaw (initialShape h.val) (below (initialShape h.val))[b.val] : ℝ)
      else 0) = _
  exact Fin.sum_univ_fun_getElem _
    (fun u : Shape => if u s = k.val then (stageALaw (initialShape h.val) u : ℝ) else 0)

theorem canonicalSideMass_stageB {K : ℕ} (h : APositive K) (s : Fin 3) :
    canonicalSideMass (.stageB h) s =
      (stageBMarginalLaw (aShape h.val) h.property s).mass := by
  funext k
  rw [show (stageBMarginalLaw (aShape h.val) h.property s).mass k =
      marginal (below (aShape h.val))
        (fun u => (stageBLaw (aShape h.val) u : ℝ)) s k from
    indexedMarginalLaw_mass _ _ _ _ _ _ k]
  change (∑ b : BSplit h, if (below (aShape h.val))[b.val] s = k.val
      then (stageBLaw (aShape h.val) (below (aShape h.val))[b.val] : ℝ)
      else 0) = _
  exact Fin.sum_univ_fun_getElem _
    (fun u : Shape => if u s = k.val then (stageBLaw (aShape h.val) u : ℝ) else 0)

theorem canonicalSideMass_stageC {K : ℕ} (h : PartC K) (s : Fin 3) :
    canonicalSideMass (.stageC h) s =
      AllFieldStageCCapacity.stageCMarginal (cParameterParent h) (cShapeParent h) s := rfl

theorem workCapacity_first {K : ℕ} (w : PlacedWork K) :
    workCapacity w.1 0 = finiteEntropy
      (JointPopulationRates.sideMass (placedLaw w).mass (w.physicalOrder 0)) := by
  rw [placedLaw_priority_sideMass]
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h =>
      rw [canonicalSideMass_stageA]
      exact stageACapacity_first_entropy _ h.property
  | stageB h =>
      rw [canonicalSideMass_stageB]
      exact stageBCapacity_first_entropy _ h.property
  | stageC h =>
      rw [canonicalSideMass_stageC]
      exact workCapacity_stageC h 0

theorem workCapacity_stageC_physical {K : ℕ} (h : PartC K)
    (phi : Placement) (i : Fin 3) :
    workCapacity (.stageC h) i = finiteEntropy
      (JointPopulationRates.sideMass (placedLaw (.stageC h, phi)).mass
        ((PlacedWork.physicalOrder (.stageC h, phi)) i)) := by
  rw [placedLaw_priority_sideMass, canonicalSideMass_stageC]
  exact workCapacity_stageC h i

theorem order_first_capacity {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) :
    workCapacity h.val.val.1 0 = finiteEntropy
      (JointPopulationRates.sideMass (orderLaw h).mass (sigma 0)) := by
  have hh := workCapacity_first h.val.val
  rw [h.property] at hh
  exact hh

def orderEntropyRate {K tick : ℕ} (allocation : Allocation) (sigma : Placement) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass

def orderNativeDegree {K tick : ℕ} (allocation : Allocation) (sigma : Placement)
    (i : Fin 3) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      (finiteEntropy (orderLaw h).mass - workCapacity h.val.val.1 i)

theorem order_entropy_sub_native_degree (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) :
    orderEntropyRate (K := K) (tick := tick) allocation sigma -
      max (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)
        (max (orderNativeDegree (K := K) (tick := tick) allocation sigma 1)
          (orderNativeDegree (K := K) (tick := tick) allocation sigma 2)) =
      (populationLength (K := K) allocation 1 : ℝ) *
        ((1 / 6 : ℝ) * Staggering.minCapacity
          (FiniteSchedule.tickCapacity K nativeLA nativeLB
            (nativeLC (fun i => (allocation.mass i : ℝ))) tick)) := by
  unfold orderEntropyRate orderNativeDegree
  rw [JointCapacityAlgebra.weighted_joint_capacity]
  simp_rw [order_dilation_capacity, ← mul_assoc]
  exact PhysicalOrders.minCapacity_mul _ _ (by positivity)

end MatrixMultiplication.AllFieldActiveCapacity

end

end OAI
