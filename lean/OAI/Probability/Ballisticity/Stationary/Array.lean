import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayTopology

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal ENNReal BigOperators Classical
namespace DirectionalTransience

instance row_compact (d : ℕ) : CompactSpace (Row d) := by
  apply isCompact_iff_compactSpace.mp
  have hbox : IsCompact {p : Direction d → ℝ≥0 | ∀ e, p e∈Set.Icc 0 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (isClosed_eq (by fun_prop) continuous_const)
  intro p hp e
  exact ⟨bot_le, (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ e)).trans_eq hp⟩

def horizontalSubgroup {d : ℕ} (e : Direction d) : AddSubgroup (Lattice d) where
  carrier := {x | x e.1=0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change x e.1=0 at hx
    change y e.1=0 at hy
    change x e.1+y e.1=0
    simp only [hx,hy,add_zero]
  neg_mem' {x} hx := by
    change x e.1=0 at hx
    change -x e.1=0
    simp only [hx,neg_zero]

abbrev HorizontalSpace {d : ℕ} (e : Direction d) := horizontalSubgroup e

abbrev ActualEpisodeArray {d : ℕ} (e : Direction d) :=
  StationaryCompact.EpisodeArray (HorizontalSpace e) (Row d)

instance actualArray_compact {d : ℕ} (e : Direction d) : CompactSpace (ActualEpisodeArray e) := inferInstance
instance actualArray_metrizable {d : ℕ} (e : Direction d) : MetrizableSpace (ActualEpisodeArray e) := inferInstance

end DirectionalTransience

end

end OAI
