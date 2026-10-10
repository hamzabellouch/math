import Mathlib
import OAI.Combinatorics.KMedian.Machines.BlockRotation

namespace OAI

section Inline_PCPRotationExt
namespace MetricKMedian.PCP.Compiler.RotationTable
open scoped Classical

variable {D B : Type} [Fintype D] [Inhabited D] [Fintype B] [Inhabited B]
lemma lookup_getElem {R : RotationTable D} (v : ℕ) (hv : v<R.length)
    (hrow : R[v].length=Fintype.card D) (j : ℕ) (hj : j<Fintype.card D) :
    lookup R v ((Fintype.equivFin D).symm ⟨j,hj⟩)=R[v][j]'(hrow.symm ▸ hj) := by
  simp only [lookup,Equiv.apply_symm_apply,List.getElem?_eq_getElem hv,
    Option.getD_some,List.getElem?_eq_getElem (hrow.symm ▸ hj)]
lemma ext_lookup {R S : RotationTable D} (hlen : R.length=S.length)
    (hR : ∀ row∈R, row.length=Fintype.card D) (hS : ∀ row∈S, row.length=Fintype.card D)
    (h : ∀ v, v<R.length → ∀ d, lookup R v d=lookup S v d) : R=S := by
  apply List.ext_getElem hlen
  intro i hi hj
  have hr := hR _ (List.getElem_mem hi)
  have hs := hS _ (List.getElem_mem hj)
  apply List.ext_getElem (hr.trans hs.symm)
  intro j hj hk
  have hd : j<Fintype.card D := hj.trans_eq hr
  exact (lookup_getElem i hi hr j hd).symm.trans
    ((h i hi ((Fintype.equivFin D).symm ⟨j,hd⟩)).trans (lookup_getElem i _ hs j hd))
omit [Inhabited D] [Inhabited B]
lemma blockRows_length (N : ℕ) (f : ℕ → B → D → ℕ × D) :
    (blockRows N f).length=N*Fintype.card B := by
  unfold blockRows
  rw [length_flatMap_uniform _ _ (Fintype.card B)
    (by intro v hv; simp only [List.length_map,ports_length]),List.length_range]
lemma blockRows_row_length (N : ℕ) (f : ℕ → B → D → ℕ × D) :
    ∀ row∈blockRows N f, row.length=Fintype.card D := by
  intro row hr
  obtain ⟨v,hv,hb⟩ := List.mem_flatMap.mp hr
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hb
  simp only [List.length_map,ports_length]
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationExt

end OAI
