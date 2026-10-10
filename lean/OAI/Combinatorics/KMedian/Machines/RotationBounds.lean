import Mathlib
import OAI.Combinatorics.KMedian.Machines.RawRotation

namespace OAI

section Inline_PCPRotationBounds
namespace MetricKMedian.PCP.Compiler.RotationTable
open Binary Binary.Automatic Finset
open scoped BigOperators Classical

variable {D : Type} [Fintype D] [Inhabited D]
def WellFormed (R : RotationTable D) : Prop :=
  ∀ row ∈ R, row.length=Fintype.card D ∧ ∀ q∈row, q.1<R.length
lemma lookup_lt {R : RotationTable D} (h : WellFormed R) (v : ℕ) (hv : v<R.length) (d : D) :
    (lookup R v d).1<R.length := by
  have hr := h R[v] (List.getElem_mem hv)
  have hd : (Fintype.equivFin D d).val<R[v].length := by rw [hr.1]; exact (Fintype.equivFin D d).isLt
  simpa only [lookup,List.getElem?_eq_getElem hv,Option.getD_some,List.getElem?_eq_getElem hd]
    using hr.2 _ (List.getElem_mem hd)
omit [Inhabited D]
lemma table_wellFormed {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) :
    WellFormed (table G e) := by
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  constructor
  · simp only [List.length_map,ports_length]
  · intro q hq
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hq
    simpa only [table_length] using (e (G.step (e.symm i) d)).isLt
variable [Coding D]
noncomputable def codeBound : ℕ := ∑ d : D, (enc d).length
lemma code_le (d : D) : (enc d).length ≤ codeBound (D := D) := by
  unfold codeBound
  exact single_le_sum (f := fun d : D => (enc d).length) (fun _ _ => Nat.zero_le _) (mem_univ d)
noncomputable def sizeBound (N : ℕ) : ℕ :=
  N*(2*(Fintype.card D*(2*(2*(N+1)+1+codeBound (D := D))+1))+1)
lemma size_bound {R : RotationTable D} (h : WellFormed R) (N : ℕ) (hN : R.length ≤ N) :
    (enc R).length ≤ sizeBound (D := D) N := by
  have he (q : ℕ × D) (hq : q.1<R.length) : (enc q).length ≤ 2*(N+1)+1+codeBound (D := D) := by
    have hn : q.1.bits.length ≤ N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
    have hd := code_le q.2
    change (encodePair Nat.bits enc q).length ≤ _
    rw [encodePair_length]
    omega
  have hr (row : List (ℕ × D)) (hm : row∈R) :
      (enc row).length ≤ Fintype.card D*(2*(2*(N+1)+1+codeBound (D := D))+1) := by
    change (encodeList (enc (α := ℕ × D)) row).length ≤ _
    have hh := h row hm
    simpa only [hh.1] using EncodedList.length_bound enc row _ (fun q hq => he q (hh.2 q hq))
  change (encodeList (enc (α := List (ℕ × D))) R).length ≤ _
  exact (EncodedList.length_bound enc R _ hr).trans (Nat.mul_le_mul_right _ hN)
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationBounds

end OAI
