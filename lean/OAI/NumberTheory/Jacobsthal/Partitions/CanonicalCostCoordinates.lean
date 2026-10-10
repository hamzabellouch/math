import OAI.NumberTheory.Jacobsthal.Estimates.LowStateHorizon
import OAI.NumberTheory.Jacobsthal.Paths.CanonicalUniformMissingVisit

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CanonicalCostCoordinates

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures FinitePathGeometry LowStateHorizon
open Erdos970Dependency.MarkedVisits

theorem raw_cost_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      (rawLast (k+1) y).2 = (y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩).2 +
        cost (stateRatio (rawLast (k+1) y).1) := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h,
      (rawLast (k+1) y).2 = (rawLast k h).2 + cost (stateRatio (rawLast (k+1) y).1) := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_eq_fun measurable_snd
        (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst))))).mp
    rw [rawExtension_last_step]
    exact costKernel_time_update _
  filter_upwards [hs,rawExtension_retains_prefix k.le_succ h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩ = rawLast k h at he
  rw [he]
  exact hy

theorem raw_cost_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).2 =
        (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 +
          cost (stateRatio (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).1) := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      (rawLast (k+1) y).2 = (y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩).2 +
        cost (stateRatio (rawLast (k+1) y).1)} :=
    measurableSet_eq_fun (measurable_snd.comp (rawLast_measurable _))
      ((measurable_snd.comp (measurable_pi_apply _)).add
        (cost_measurable.comp (stateRatio_measurable.comp
          (measurable_fst.comp (rawLast_measurable _)))))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega)) = rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      (rawLast (k+1) y).2 = (y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩).2 +
        cost (stateRatio (rawLast (k+1) y).1) := by
    have hc : rawExtension a (k+1) = rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (raw_cost_step k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

end NumberTheoryLean.CanonicalCostCoordinates

end

end Erdos970

end OAI
