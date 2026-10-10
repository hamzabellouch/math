import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitSampler
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastUnit

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def fastSelected (x : Context×Bits) : ℕ×ℕ := fastDraw (x.1,x.2.getD (x.1.1.1.length-1) [])
def fastSelectedRealizer : Realizer fastSelected := by
  let n : Realizer (fun x : Context×Bits=>x.1.1.1.length-1) := composition (composition first.fst.fst listLength) predecessor
  exact (composition (pair first (composition (pair second n) (getDFast []))) fastDrawRealizer).congr (fun _=>rfl)
lemma polynomial_fastSelected : PolynomialTime fastSelectedRealizer := by
  unfold fastSelectedRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_fastDraw
  have := polynomial_getDFast ([] : List Bool)
  have := polynomial_predecessor
  dsimp only [Realizer.fst,Realizer.snd]
  tree_poly

def nextContextFast : Realizer nextContext :=
  (pair (pair (composition (pair first.fst.fst second.fst) residualFast) first.fst.snd) first.snd).congr (fun _=>rfl)
lemma polynomial_nextContextFast : PolynomialTime nextContextFast := by
  unfold nextContextFast
  apply polynomial_congr
  have := polynomial_residualFast
  dsimp only [Realizer.fst,Realizer.snd]
  tree_poly

def fastStep (x : State) : State :=
  if 2≤x.1.1.1.length then
    let c:=fastSelected (x.1,x.2.1)
    (nextContext (x.1,c),(x.2.1,(x.1.1.1.length-2,c)::x.2.2))
  else x
def fastStepRealizer : Realizer fastStep := by
  let n : Realizer (fun x : State=>x.1.1.1.length) := composition first.fst.fst listLength
  let c : Realizer (fun x : State=>fastSelected (x.1,x.2.1)) := (composition (f:=fun x : State=>(x.1,x.2.1)) (pair first second.fst) fastSelectedRealizer).congr (fun _=>rfl)
  let ctx := composition (pair first c) nextContextFast
  let k := composition (pair n (constant 2)) subtract
  let fs := composition (pair (pair k c) second.snd) listCons
  let r := pair ctx (pair second.fst fs)
  exact (choose (composition (composition (pair n (constant 2)) less) boolNot) r identity).congr (by
    intro x; simp [fastStep,Nat.succ_le_iff])
lemma polynomial_fastStep : PolynomialTime fastStepRealizer := by
  unfold fastStepRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_fastSelected
  have := polynomial_nextContextFast
  dsimp only [Realizer.fst,Realizer.snd]
  tree_poly

lemma chooseBits_le_length (x : List TreeFraction.Fraction×List Bool) : ExecutableChoice.chooseBits x≤x.1.length := by
  exact TreeTyped.listMin_le_default _ _
lemma fastDraw_bounds (x : Context×List Bool) :
    (fastDraw x).1≤x.1.1.1.length*x.1.1.2.length ∧ (fastDraw x).2≤x.1.1.1.length*x.1.1.2.length := by
  have h:=chooseBits_le_length (fastProbabilities x.1,x.2)
  simp only [fastProbabilities,List.length_map,List.length_range] at h
  exact ⟨(Nat.div_le_self _ _).trans h,(Nat.mod_le _ _).trans h⟩
lemma fastSelected_bounds (x : Context×Bits) :
    (fastSelected x).1≤x.1.1.1.length*x.1.1.2.length ∧ (fastSelected x).2≤x.1.1.1.length*x.1.1.2.length :=
  fastDraw_bounds _
lemma residual_length (bs : Bags) (b : ℕ) : (residual (bs,b)).length=bs.length-2 := by
  simp [residual]
lemma residual_mem {bs : Bags} {b : ℕ} {a : Bag} (ha : a∈residual (bs,b)) : a∈bs := by
  simp only [residual,List.mem_map,List.mem_range] at ha
  obtain ⟨i,hi,rfl⟩:=ha
  have hj : skip (i,b)<bs.length := by simp only [skip]; split_ifs <;> omega
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

def DescentInvariant (a : Context×Bits) (k : ℕ) (z : State) : Prop :=
  z.1.1.1.length≤a.1.1.1.length ∧
  (∀ b∈z.1.1.1,b∈a.1.1.1) ∧ z.1.1.2=a.1.1.2 ∧ z.1.2=a.1.2 ∧ z.2.1=a.2 ∧
  z.2.2.length+k≤a.1.1.1.length ∧
  ∀ f∈z.2.2,f.1≤a.1.1.1.length ∧ f.2.1≤a.1.1.1.length*a.1.1.2.length ∧ f.2.2≤a.1.1.1.length*a.1.1.2.length
lemma descent_init (a : Context×Bits) : DescentInvariant a a.1.1.1.length (a.1,(a.2,[])) := by
  simp only [DescentInvariant,List.length_nil,Nat.zero_add,List.not_mem_nil,IsEmpty.forall_iff,le_refl,implies_true,true_and,and_true]
  exact fun b h=>h
lemma descent_step (a : Context×Bits) (k : ℕ) (z : State) (hz : DescentInvariant a (k+1) z) :
    DescentInvariant a k (fastStep z) := by
  obtain ⟨hl,hb,hp,ho,ht,hf,hm⟩:=hz
  by_cases hn : 2≤z.1.1.1.length
  · rw [fastStep,ite_eq_left hn]
    have hc:=fastSelected_bounds (z.1,z.2.1)
    rw [hp] at hc
    have hmul:=Nat.mul_le_mul_right a.1.1.2.length hl
    refine ⟨?_,?_,hp,ho,ht,?_,?_⟩
    · change (residual (z.1.1.1,(fastSelected (z.1,z.2.1)).1)).length≤_
      rw [residual_length]; omega
    · intro b hb'
      exact hb b (residual_mem hb')
    · change ( _ :: z.2.2).length+k≤_
      simp only [List.length_cons]; omega
    · intro f hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨(Nat.sub_le _ _).trans hl,hc.1.trans hmul,hc.2.trans hmul⟩
      · exact hm f hh
  · rw [fastStep,ite_eq_right hn]
    exact ⟨hl,hb,hp,ho,ht,by omega,hm⟩

lemma descent_weight (a : Context×Bits) (k : ℕ) (z : State) (hz : DescentInvariant a k z) :
    weight z≤ 20*(weight a+1)^3 := by
  obtain ⟨hl,hb,hp,ho,ht,hf,hm⟩:=hz
  let S:=weight a
  have hn : a.1.1.1.length≤S := (list_length_le_weight _).trans ((weight_fst a.1.1).trans ((weight_fst a.1).trans (weight_fst a)))
  have hn' : a.1.1.2.length≤S := (list_length_le_weight _).trans ((weight_snd a.1.1).trans ((weight_fst a.1).trans (weight_fst a)))
  have hbn:weight z.1.1.1≤S*(S+1)+1 := by
    have hh:=weight_map_bound (as:=z.1.1.1) (f:=id) (N:=S) (fun b hh=>(weight_mem (hb b hh)).trans ((weight_fst a.1.1).trans ((weight_fst a.1).trans (weight_fst a))))
    simpa only [List.map_id] using hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (S+1) (hl.trans hn)) 1)
  have hmfn:weight z.2.2≤S*(8*S*S+4*S+6)+1 := by
    have hh:=weight_map_bound (as:=z.2.2) (f:=id) (N:=8*S*S+4*S+5) (by
      intro f hh
      obtain ⟨h1,h2,h3⟩:=hm f hh
      have hm:=Nat.mul_le_mul hn hn'
      have hf1:=weight_nat_numeric f.1
      have hf2:=weight_nat_numeric f.2.1
      have hf3:=weight_nat_numeric f.2.2
      change weight f≤_
      rw [←Prod.eta f,weight_prod,←Prod.eta f.2,weight_prod]
      nlinarith)
    simp only [List.map_id] at hh
    have hlen :z.2.2.length≤S:=by omega
    have he : 8*S*S+4*S+5+1=8*S*S+4*S+6 := by omega
    rw [he] at hh
    exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hpar :weight a.1.1.2≤S := (weight_snd a.1.1).trans ((weight_fst a.1).trans (weight_fst a))
  have hplan :weight a.1.2≤S := (weight_snd a.1).trans (weight_fst a)
  have hbits :weight a.2≤S := weight_snd a
  rw [←Prod.eta z,weight_prod,←Prod.eta z.1,weight_prod,←Prod.eta z.1.1,weight_prod,←Prod.eta z.2,weight_prod,hp,ho,ht]
  change _≤20*(S+1)^3
  nlinarith

def fastDescend (a : Context×Bits) : State :=
  countDown (fun y : ℕ×State=>fastStep y.2) a.1.1.1.length (a.1,(a.2,[]))
def fastDescendRealizer : Realizer fastDescend :=
  (composition (pair (composition first.fst.fst listLength) (pair first (pair second (constant ([] : List Frame)))))
    (iterateDown (composition second fastStepRealizer))).congr (fun _=>rfl)
lemma polynomial_fastDescend : PolynomialTime fastDescendRealizer := by
  unfold fastDescendRealizer
  apply polynomial_congr
  apply polynomial_boundedRepeat (by dsimp only [Realizer.fst,Realizer.snd]; tree_poly)
    (polynomial_composition polynomial_second polynomial_fastStep)
    X (20*(X+1)^3) DescentInvariant
  · intro a
    simpa only [Function.comp_apply,Polynomial.eval_X] using (list_length_le_weight a.1.1.1).trans ((weight_fst a.1.1).trans ((weight_fst a.1).trans (weight_fst a)))
  · exact descent_init
  · intro a k _hk z hz
    exact descent_step a k z hz
  · intro a k z hz
    simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using descent_weight a k z hz
end MatchingFPRAS.ExecutableUnit

end OAI
