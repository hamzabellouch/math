import OAI.Combinatorics.HadwigerCounterexample.PairedCollisionBounds

namespace OAI

/-! # Paired Mass Identities -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K M: ℕ} {q : Format} {d e : Rates}

namespace Quill
variable {i:Bool} (w : Quill p q d i)
    (μ : Wgt (UnitType p n N)) (s : Charts p n d)
    (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (m : Mixer p n)
    (P : UnitType p n N→Prop)

def customer := fromFlags μ ((w.pen t).state z n)
  (Y:=Bool)
  (fun o x=> open scoped Classical in decide (w.deposit t z m o s x))
  ((w.pen t).resultKey)
def custom := hung (w.customer μ s t z m) (ownPart t z)

def billboard := fun (o:UnitType p n N) x=> open scoped Classical in decide (w.deposit t z m o s x)
theorem sales_core :
    w.sales t z μ P m s=flaggedW μ ((w.pen t).state z n) (w.billboard (N:=N) s t z m)
    ((w.pen t).resultKey) (fun o b=> P o ∧ b) := by
  classical
  funext x; unfold sales Volley.hist
  simp_rw [pr]; rw [avg_avg]
  unfold flaggedW mixW mapW
  apply avg_congr; intro i hi
  simp only [pr,avg,Function.comp_apply,subW,billboard,decide_eq_true_eq]
  refine Finset.sum_congr rfl fun a _=> ?_
  rw [mul_assoc,← ind_and]; rfl

theorem sales_receipt : customer w μ s t z m (w.sales t z μ P m s) :=
  ⟨_,w.sales_core μ s t z m P⟩

theorem sales_part : carried (w.sales t z μ P m s) (ownPart t z) := by
  intro o ho
  unfold sales Volley.hist
  let A:=w.pen t
  have hi (x : Inputs p n (Messenger q)) :
      pr μ (fun i=>(P i ∧ w.deposit t z m i s x)∧(A.draw x).keys t i=o) = 0 := by
    have h i : ¬((P i∧ w.deposit t z m i s x)∧(A.draw x).keys t i=o) := by
      rintro ⟨⟨hp,hg⟩,hk⟩
      apply ho; rw [←hk]; exact hg.2.2
    unfold pr;simp only [ind_zero (h _),avg_const,mul_zero]
  change avg (A.state z n) _=_
  exact (avg_congr (g:=fun _ => 0) (fun x _ => hi x)).trans (by rw [avg_const,mul_zero])

theorem sales_custom : custom w μ s t z m (w.sales t z μ P m s) := by
  let v:= w.sales t z μ P m s
  refine ⟨v,w.sales_receipt μ s t z m P, funext fun i =>?_⟩
  change v i=_
  unfold subW
  by_cases hi : ownPart t z i
  · rw [ind_one hi,mul_one]
  rw [show v i=0 from w.sales_part μ s t z m P i hi,zero_mul]

def prowl (o : UnitType p n N) (W : Wgt (Keys (p:=p) t N)) :=
    avg ((w.pen t).state z n) (fun x=>ind (w.deposit t z m o s x)*W ((w.pen t).resultKey o x))

theorem sales_mean (W : Wgt (Keys (p:=p) t N)) :
    avg (w.sales t z μ P m s) W =
      avg μ (fun o=> ind (P o) * prowl w s t z m o W) := by
  classical
  rw [sales_core, flaggedW]
  refine (mixW_avg μ _ (show Wgt (Keys (p:=p) ((w.pen t).t) N) from W)).trans ?_
  refine avg_congr fun i _ => ?_
  rw [mapW_avg]
  unfold prowl subW
  simp only [avg,Finset.mul_sum,Function.comp_apply,billboard,decide_eq_true_eq,ind_and]
  refine Finset.sum_congr rfl fun _ _=>?_
  ring

theorem sales_pos (h : ∀ x,0≤μ x) (x) : 0≤ w.sales t z μ P m s x :=
  avg_nonneg (prodW_nonneg (fun _=> normW_nonneg (subW_nonneg (spins_law ..).nz _)))
    (fun _=> pr_nonneg h)
end Quill

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

theorem arena_pos (w : Typus p q d e)
    (m: Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
    (h : 0<s.amount μ) (hw : IsLaw μ) : 0 ≤ arena v w m μ k := by
  classical
  have hf (i:s.T) : 0≤portionW μ s.T i := div_nonneg (pr_nonneg hw.nz) h.le
  have hg (S : CTile p n N) i : 0≤partW μ S i := normW_nonneg (subW_nonneg hw.nz _) _
  refine avg_nonneg (fun _=>mul_nonneg (hf _) (hf _)) (fun i=>avg_nonneg
    (unifOn_sub _).nz (fun x=>mul_nonneg ?_ ?_))
  · exact div_nonneg (w.qA.sales_pos _ _ _ _ m _ (hg _) x) ((unifOn_sub _).nz _)
  exact div_nonneg (w.qB.sales_pos _ _ _ _ m _ (hg _) x) ((unifOn_sub _).nz _)

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
