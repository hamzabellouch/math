import OAI.Combinatorics.Crossing.AxisCrossingOrder
import OAI.Combinatorics.Crossing.EvenCrossingLowerBound

namespace OAI

noncomputable section
namespace Zarankiewicz.BalancedAxisRealization
open scoped BigOperators Finset
variable {m n : ℕ} (R : BalancedAxisRealization m n)

def crossingCandidates (_R : BalancedAxisRealization m n) : Finset ((Fin m × Fin m) × (Fin n × Fin n)) :=
  balancedRayPairs m ×ˢ balancedRayPairs n

def candidateCrossings (v : (Fin m × Fin m) × (Fin n × Fin n)) : Finset Plane :=
  pairCrossings R.drawing (v.1.1,v.2.2) (v.1.2,v.2.1)

theorem pairCrossings_card_le_one (e f : BipartiteEdge m n) : (pairCrossings R.drawing e f).card ≤ 1 := by
  classical
  by_cases hef : e=f
  · subst f
    simp [pairCrossings_self]
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    have hsub := axisContinuousDrawing_pair_subsingleton R.vertical R.horizontal R.vertical_injective
      R.horizontal_injective R.vertical_ne_zero R.horizontal_ne_zero e f hef
    exact hsub (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2

theorem crossings_covered_by_candidates :
    R.drawing.crossings_finite.toFinset ⊆ R.crossingCandidates.biUnion R.candidateCrossings := by
  classical
  intro x hx
  have hcross : x ∈ crossingPoints R.drawing.toContinuousDrawing := by simpa using hx
  obtain ⟨e,f,hef,he,hf⟩ := hcross
  have hind := axisContinuousDrawing_meeting_independent R.vertical R.horizontal R.vertical_injective
    R.horizontal_injective R.vertical_ne_zero R.horizontal_ne_zero e f hef x he hf
  rcases lt_or_gt_of_ne hind.1 with hlt | hgt
  · have hc := R.meeting_balanced_pairs e.1 f.1 e.2 f.2 hlt x he hf
    apply Finset.mem_biUnion.mpr
    refine ⟨((e.1,f.1),(f.2,e.2)),Finset.mem_product.mpr hc,?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hx,hef,he,hf⟩
  · have hc := R.meeting_balanced_pairs f.1 e.1 f.2 e.2 hgt x hf he
    apply Finset.mem_biUnion.mpr
    refine ⟨((f.1,e.1),(e.2,f.2)),Finset.mem_product.mpr hc,?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hx,Ne.symm hef,hf,he⟩

theorem crossingCount_le : crossingCount R.drawing ≤ axisPairs m*axisPairs n := by
  classical
  calc
    crossingCount R.drawing ≤ (R.crossingCandidates.biUnion R.candidateCrossings).card :=
      Finset.card_le_card R.crossings_covered_by_candidates
    _ ≤ ∑ v ∈ R.crossingCandidates, (R.candidateCrossings v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ R.crossingCandidates, 1 := by
      apply Finset.sum_le_sum
      intro v hv
      exact R.pairCrossings_card_le_one _ _
    _ = R.crossingCandidates.card := by simp
    _ = axisPairs m*axisPairs n := by
      rw [crossingCandidates,Finset.card_product,balancedRayPairs_card,balancedRayPairs_card]

theorem crossingCount_eq : crossingCount R.drawing=axisPairs m*axisPairs n :=
  Nat.le_antisymm R.crossingCount_le (crossing_lower_bound m n R.drawing)

end Zarankiewicz.BalancedAxisRealization

end

end OAI
