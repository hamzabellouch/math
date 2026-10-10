import OAI.Combinatorics.Crossing.DrawingMarks
import Mathlib.Data.Finset.Sort

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_sorted_unitInterval_finset (S : Finset unitInterval)
    (h0 : (0 : unitInterval) ∈ S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧ Set.range t=(S : Set unitInterval) := by
  have hc : 1 < S.card := Finset.one_lt_card.mpr ⟨0,h0,1,h1,zero_ne_one⟩
  let k := S.card-1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : S.card=k+1 := by dsimp [k]; omega
  let e := S.orderEmbOfFin hcard
  have hrange : Set.range e=(S : Set unitInterval) := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, e i=0 := by
    have hm : (0 : unitInterval) ∈ Set.range e := hrange.symm ▸ h0
    exact hm
  obtain ⟨j,hj⟩ : ∃ j, e j=1 := by
    have hm : (1 : unitInterval) ∈ Set.range e := hrange.symm ▸ h1
    exact hm
  have he0 : e 0=0 := by
    apply le_antisymm
    · exact (e.monotone (Fin.zero_le i)).trans_eq hi
    · exact (e 0).property.1
  have he1 : e (Fin.last k)=1 := by
    apply le_antisymm
    · exact (e (Fin.last k)).property.2
    · exact hj.symm.trans_le (e.monotone (Fin.le_last j))
  exact ⟨k,hk,e,e.strictMono,he0,he1,hrange⟩

theorem exists_sorted_drawing_parameters {m n : ℕ} (D : FiniteIntersectionDrawing m n)
    (e : BipartiteEdge m n) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧
      Set.range t=(D.edge e) ⁻¹' drawingMarks D := by
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset (marked_parameters_finite D e).toFinset
    (by simpa using marked_parameter_zero D e) (by simpa using marked_parameter_one D e)
  exact ⟨k,hk,t,ht,h0,h1,by simpa using hR⟩

end Zarankiewicz

end

end OAI
