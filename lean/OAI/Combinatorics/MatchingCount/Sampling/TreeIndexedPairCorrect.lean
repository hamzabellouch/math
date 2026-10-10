import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeNumberedCodec
import OAI.Combinatorics.MatchingCount.Sampling.TreeIndexedPair

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram TreeTyped.Numbered

variable {E V : Type} [Fintype E] [LinearOrder E] [Fintype V] [LinearOrder V]
def endpointRep (s : Sym2 V) : ℕ×ℕ := (index s.inf,index s.sup)
def contextRep (ends : E→Sym2 V) (w z : E→ℚ) : Context :=
  (List.ofFn (fun i=>endpointRep (ends (UnitRefresh.orderedEnum E i))),
    (List.ofFn (fun i=>TreeFraction.repr (w (UnitRefresh.orderedEnum E i))),
     List.ofFn (fun i=>TreeFraction.repr (z (UnitRefresh.orderedEnum E i)))))
lemma endpoints_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) :
    endpoints (contextRep ends w z,index e)=endpointRep (ends e) := by
  simp [endpoints,contextRep,index,List.getD_eq_getElem?_getD]
lemma u_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) :
    u (contextRep ends w z,index e)=TreeFraction.repr (w e) := by
  simp [u,contextRep,index,List.getD_eq_getElem?_getD]
lemma v_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) :
    v (contextRep ends w z,index e)=TreeFraction.repr (z e) := by
  simp [v,contextRep,index,List.getD_eq_getElem?_getD]
omit [Fintype V] in
lemma pair_inf_sup [Fintype V] (s : Sym2 V) : s(s.inf,s.sup)=s := Sym2.sortEquiv.symm_apply_apply s
lemma incident_rep (s : Sym2 V) (x : V) :
    incident (endpointRep s,index x)=decide (x∈s) := by
  simp only [incident,endpointRep,(index_injective (A:=V)).eq_iff]
  congr 1
  rw [←pair_inf_sup s,Sym2.mem_iff]
  simp only [Sym2.inf_mk,Sym2.sup_mk]
  rw [min_eq_left (Sym2.inf_le_sup s),max_eq_right (Sym2.inf_le_sup s)]
  exact propext (by tauto)
lemma same_rep (s t : Sym2 V) :
    same (endpointRep s,endpointRep t)=decide (s=t) := by
  simp only [same,endpointRep,(index_injective (A:=V)).eq_iff]
  congr 1
  exact propext (by rw [←Sym2.eq_iff,pair_inf_sup,pair_inf_sup])
lemma same_pair_rep (s : Sym2 V) (a b : V) :
    same (endpointRep s,(index a,index b))=decide (s=s(a,b)) := by
  simp only [same,endpointRep,(index_injective (A:=V)).eq_iff]
  congr 1
  exact propext (by rw [←Sym2.eq_iff,pair_inf_sup])
lemma adjacent_rep (s t : Sym2 V) :
    adjacent (endpointRep s,endpointRep t)=decide (∃ v,v∈s ∧ v∈t) := by
  simp only [adjacent,endpointRep]
  change (incident (endpointRep s,index t.inf) || incident (endpointRep s,index t.sup))=_
  rw [incident_rep,incident_rep]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro (h|h)
    · refine ⟨t.inf,h,?_⟩
      simpa only [pair_inf_sup] using (Sym2.mem_mk_left t.inf t.sup)
    · refine ⟨t.sup,h,?_⟩
      simpa only [pair_inf_sup] using (Sym2.mem_mk_right t.inf t.sup)
  · rintro ⟨a,ha,ht⟩
    rw [←pair_inf_sup t,Sym2.mem_iff] at ht
    rcases ht with h|h <;> subst a <;> simp [ha]

lemma p_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) (x : V) :
    p (contextRep ends w z,(index e,index x))=decide (x∈ends e) := by
  unfold p
  rw [endpoints_rep,incident_rep]
lemma q_rep (ends : E→Sym2 V) (w z : E→ℚ) (e f : E) :
    q (contextRep ends w z,(index e,index f))=decide (ends e=ends f) := by
  unfold q
  rw [endpoints_rep,endpoints_rep,same_rep]
lemma r_rep (ends : E→Sym2 V) (w z : E→ℚ) (e : E) (a b : V) :
    r (contextRep ends w z,(index e,(index a,index b)))=decide (ends e=s(a,b)) := by
  unfold r
  rw [endpoints_rep,same_pair_rep]
lemma t_rep (ends : E→Sym2 V) (w z : E→ℚ) (e f : E) :
    t (contextRep ends w z,(index e,index f))=decide (∃ v,v∈ends e ∧ v∈ends f) := by
  unfold t
  rw [endpoints_rep,endpoints_rep,adjacent_rep]
end MatchingFPRAS.ExecutablePair

end OAI
