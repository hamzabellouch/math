import Mathlib
import OAI.Combinatorics.KMedian.Geometry.FixedBatchTransition
import OAI.Combinatorics.KMedian.Process.FiniteGraph

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem relevant_card_bound (D : Actions I E) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ)
    (hsource : (D.ordinary : Set E).InjOn D.source)
    (hin : ∀ i ∈ S, (FiniteGraph.incoming D.erase i).card ≤ Δ) :
    (relevant D S).card ≤ Δ^2+Δ := by
  let U := D.ordinary.filter (fun e => D.source e ∈ S)
  have hU : U.card ≤ S.card := by
    apply card_le_card_of_injOn D.source
    · intro e he
      exact (mem_filter.mp he).2
    · intro e he f hf hef
      exact hsource (mem_filter.mp he).1 (mem_filter.mp hf).1 hef
  have heq : relevant D S=U ∪ FiniteGraph.touching D.erase S := by
    ext e
    simp only [mem_relevant, mem_union, U, mem_filter, FiniteGraph.mem_touching,
      nonempty_def, mem_inter]
  rw [heq]
  calc
    _ ≤ U.card+(FiniteGraph.touching D.erase S).card := card_union_le _ _
    _ ≤ S.card+S.card*Δ := Nat.add_le_add hU (FiniteGraph.touching_card _ _ hin)
    _ ≤ Δ+Δ*Δ := Nat.add_le_add hS (Nat.mul_le_mul_right Δ hS)
    _ = Δ^2+Δ := by ring

omit [DecidableEq I] in
                                                                        
theorem card_le_grid {g : ℝ} {Δ : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (S : Finset I) (hm : mass g S ≤ 1) : S.card ≤ Δ := by
  have hreal : (S.card:ℝ) ≤ (Δ:ℝ) := by
    apply (mul_le_mul_iff_right₀ hg).mp
    simpa only [mass, hunit] using hm
  exact_mod_cast hreal

theorem split_incoming_bound (D : Actions I E) (Full : Actions I H) (parent : E → H)
    (hp : ∀ h, (↑(univ.filter (fun e => parent e=h)) : Set E).PairwiseDisjoint D.erase)
    (hu : ∀ h, (univ.filter (fun e => parent e=h)).biUnion D.erase=Full.erase h)
    (i : I) :
    (FiniteGraph.incoming D.erase i).card ≤ (FiniteGraph.incoming Full.erase i).card := by
  apply card_le_card_of_injOn parent
  · intro e he
    have hie : i ∈ D.erase e := (mem_filter.mp he).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [← hu (parent e)]
    exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, rfl⟩, hie⟩
  · intro e he f hf hef
    by_contra hne
    have hdis := hp (parent e) (show e ∈ univ.filter (fun a => parent a=parent e) by simp)
      (show f ∈ univ.filter (fun a => parent a=parent e) by simp [hef]) hne
    exact (disjoint_left.mp hdis) ((mem_filter.mp he).2) ((mem_filter.mp hf).2)

end MetricKMedian.FixedBatch
end
end

end OAI
