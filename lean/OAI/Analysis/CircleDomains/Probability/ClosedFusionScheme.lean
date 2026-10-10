import Mathlib.Topology.MetricSpace.CantorScheme
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Nested closed sets with uniformly shrinking children give a continuous
branch-limit map on Baire space. This is the topological part of law fusion. -/

open Set Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

structure ClosedFusionScheme (Z : Type*) [MetricSpace Z] where
  carrier : List ℕ → Set Z
  closed : ∀ l, IsClosed (carrier l)
  nonempty : ∀ l, (carrier l).Nonempty
  child_subset : ∀ l a, carrier (a :: l) ⊆ carrier l
  child_dist : ∀ l a, ∀ x ∈ carrier (a :: l), ∀ y ∈ carrier (a :: l),
    dist x y ≤ 1 / ((l.length : ℝ) + 1)

namespace ClosedFusionScheme

variable {Z : Type*} [MetricSpace Z] (S : ClosedFusionScheme Z)

theorem vanishingDiam : CantorScheme.VanishingDiam S.carrier := by
  intro x
  have hb (n : ℕ) : Metric.ediam (S.carrier (PiNat.res x (n + 1))) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [PiNat.res_succ]
    apply Metric.ediam_le_of_forall_dist_le
    intro z hz w hw
    simpa only [PiNat.res_length] using S.child_dist (PiNat.res x n) (x n) z hz w hw
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs : Tendsto (fun n : ℕ => Metric.ediam (S.carrier (PiNat.res x (n + 1))))
      atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) hb
  exact (tendsto_add_atTop_iff_nat 1).mp hs

variable [CompleteSpace Z]

theorem total : (CantorScheme.inducedMap S.carrier).1 = univ :=
  CantorScheme.ClosureAntitone.map_of_vanishingDiam S.vanishingDiam
    (CantorScheme.Antitone.closureAntitone S.child_subset S.closed) S.nonempty

def limit (x : ℕ → ℕ) : Z :=
  (CantorScheme.inducedMap S.carrier).2 ⟨x, S.total.symm ▸ mem_univ x⟩

theorem limit_mem (x : ℕ → ℕ) (n : ℕ) : S.limit x ∈ S.carrier (PiNat.res x n) :=
  CantorScheme.map_mem _ n

theorem continuous_limit : Continuous S.limit :=
  S.vanishingDiam.map_continuous.comp (continuous_id.subtype_mk _)

end ClosedFusionScheme
end CircleDomainRigidity

end

end OAI
