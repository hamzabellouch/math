import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeRationalWeight
import OAI.Combinatorics.MatchingCount.Algorithm.TreeObservables

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction

variable {C E : Type} [LinearOrder E]

lemma zeroMarks_rep (s : Finset E) (m : E→Fin 3) :
    zeroMarks (marksRep s m)=true ↔ ∀ e∈s,m e=0 := by
  simp only [zeroMarks,marksRep,List.all_map,List.all_eq_true,Function.comp_apply,
    decide_eq_true_eq,Finset.mem_sort]
  constructor
  · intro h e he; exact Fin.ext (h e he)
  · intro h e he; exact congrArg Fin.val (h e he)

lemma probeFlag_rep (s : Finset E) (m : E→Fin 3) (e : E) :
    probeFlag (e,marksRep s m)=true ↔ e∈s ∧ ∀ a∈s,m a=if a=e then 2 else 0 := by
  simp only [probeFlag,marksRep,Bool.and_eq_true,List.any_map,List.all_map,List.any_eq_true,
    List.all_eq_true,Function.comp_def,probeExpected]
  constructor
  · rintro ⟨⟨a,ha,hae⟩,h⟩
    have hae' : a=e := of_decide_eq_true hae
    subst a
    refine ⟨(Finset.mem_sort (·≤·)).mp ha,fun b hb=>Fin.ext ?_⟩
    have hh:=of_decide_eq_true (h b ((Finset.mem_sort (·≤·)).mpr hb))
    by_cases hbe : b=e <;> simp [hbe] at hh ⊢ <;> exact hh
  · rintro ⟨he,h⟩
    refine ⟨⟨e,(Finset.mem_sort (·≤·)).mpr he,by simp⟩,fun b hb=>?_⟩
    apply decide_eq_true
    have hh:=congrArg Fin.val (h b ((Finset.mem_sort (·≤·)).mp hb))
    by_cases hbe : b=e <;> simp [hbe] at hh ⊢ <;> exact hh

lemma weighted_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0≤r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e))
    (s : Finset E) (m : E→Fin 3) :
    weighted q (c,marksRep s m)=TreeFraction.repr (∏ e∈s,r e) := by
  unfold weighted marksRep
  simp only [List.map_map]
  exact TreeTyped.SparseProgram.weight_repr q c r hr hq s

lemma eraseMark_rep (s : Finset E) (m : E→Fin 3) (e : E) :
    eraseMark (e,marksRep s m)=marksRep (s\{e}) m := by
  unfold eraseMark marksRep
  simp only [List.filter_map]
  congr 1
  apply List.Pairwise.eq_of_mem_iff (s.sortedLT_sort.pairwise.filter _) (Finset.sortedLT_sort _).pairwise
  intro a
  simp

lemma observableA_rep (s : Finset E) (m : E→Fin 3) :
    observableA (marksRep s m)=TreeFraction.repr (if ∀ e∈s,m e=0 then (1:ℚ) else 0) := by
  unfold observableA
  simp only [zeroMarks_rep]
  split_ifs <;> rfl
lemma observableD_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0≤r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e))
    (s : Finset E) (m : E→Fin 3) :
    observableD q (c,marksRep s m)=
      TreeFraction.repr (if ∀ e∈s,m e=0 then ∏ e∈s,r e else 0) := by
  unfold observableD
  simp only [zeroMarks_rep]
  split_ifs
  · exact weighted_rep q c r hr hq s m
  · rfl
lemma observableProbe_rep (q : C×E→Fraction) (c : C) (r : E→ℚ)
    (hr : ∀ e,0≤r e) (hq : ∀ e,q (c,e)=TreeFraction.repr (r e))
    (s : Finset E) (m : E→Fin 3) (e : E) :
    observableProbe q (c,(e,marksRep s m))=
      TreeFraction.repr (if e∈s ∧ ∀ a∈s,m a=if a=e then 2 else 0 then ∏ a∈s\{e},r a else 0) := by
  unfold observableProbe
  simp only [probeFlag_rep]
  split_ifs
  · rw [eraseMark_rep]
    exact weighted_rep q c r hr hq _ m
  · rfl
end MatchingFPRAS.ExecutableMarking

end OAI
