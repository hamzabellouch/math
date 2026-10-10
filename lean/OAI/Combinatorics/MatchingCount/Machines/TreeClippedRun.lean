import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeClippedDP

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

abbrev CappedState := CountInput×State

def cappedStep (x : ℕ×CappedState) : CappedState :=
  let o:=x.2.1
  let st:=x.2.2
  let rem:=st.1-1
  (o,(rem,(trim st.2.1 x.1,cappedUpdate ((o,((st.2.1,o.1.2),(x.1,st.2.2))),rem))))
def cappedStepRealizer : Realizer cappedStep := by
  let o : Realizer (fun x : ℕ×CappedState=>x.2.1) := second.fst
  let st : Realizer (fun x : ℕ×CappedState=>x.2.2) := second.snd
  let rem := composition st.fst predecessor
  let bs := composition (pair st.snd.fst first) trimRealizer
  let inp := pair (pair o (pair (pair st.snd.fst o.fst.snd) (pair first st.snd.snd))) rem
  exact (pair o (pair rem (pair bs (composition inp cappedUpdateRealizer)))).congr (fun _=>rfl)
lemma polynomial_cappedStep : PolynomialTime cappedStepRealizer := by
  unfold cappedStepRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_trim
  have := polynomial_cappedUpdate
  tree_poly

def tableWeightBound (o : CountInput) : ℕ :=
  1+nLabels o*(2+(nVertices o*nPlan o+1)*(4*capBits o+2))
lemma cappedUpdate_weight (x : UpdateInput) : weight (cappedUpdate x)≤tableWeightBound x.1.1 := by
  unfold cappedUpdate tabulate
  have hw:=weight_map_bound (as:=List.range (updateRows x))
    (f:=fun a=>(List.range (updateColumns x+1)).map fun r=>cappedEntry (x,(a,r)))
    (N:=1+(nVertices x.1.1*nPlan x.1.1+1)*(4*capBits x.1.1+2)) (by
      intro a _
      have hh:=weight_map_bound (as:=List.range (updateColumns x+1))
        (f:=fun r=>cappedEntry (x,(a,r))) (N:=4*capBits x.1.1+1) (by
          intro r _
          have hb:=clip_size (capBits x.1.1) (rawEntry (x.1.2,(a,r)))
          have hw:=weight_nat_le (cappedEntry (x,(a,r)))
          change (cappedEntry (x,(a,r))).size≤capBits x.1.1 at hb
          omega)
      simp only [List.length_range] at hh
      simp only [Nat.add_assoc, Nat.reduceAdd] at hh
      have hdim : updateColumns x≤nVertices x.1.1*nPlan x.1.1 := Nat.mul_le_mul_left _ (min_le_right _ _)
      have hm:=Nat.mul_le_mul_right (4*capBits x.1.1+2) (Nat.add_le_add_right hdim 1)
      exact hh.trans (by omega))
  simp only [List.length_range,updateRows] at hw
  unfold tableWeightBound
  dsimp only
  exact hw.trans_eq (by ring)
lemma tableWeightBound_polynomial (o : CountInput) :
    tableWeightBound o≤1+weight o*(2+((weight o)^2+1)*(4*((weight o)^2+(weight o)^5+1)+2)) := by
  obtain ⟨hn,hm,hL⟩:=input_lengths o
  have hb:=capBits_bound o
  have hprod : nVertices o*nPlan o≤(weight o)^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hL
  unfold tableWeightBound
  exact Nat.add_le_add_left (Nat.mul_le_mul hm (Nat.add_le_add_left (Nat.mul_le_mul
    (Nat.add_le_add_right hprod 1) (by omega)) 2)) 1

lemma cappedFold_invariant (ls : List ℕ) (z : CappedState) :
    let r:=ls.foldl (fun z l=>cappedStep (l,z)) z
    r.1=z.1 ∧ r.2.1≤z.2.1 ∧ r.2.2.1.Sublist z.2.2.1 ∧
      weight r.2.2.2≤weight z.2.2.2+tableWeightBound z.1 := by
  induction ls generalizing z with
  | nil => exact ⟨rfl,le_rfl,List.Sublist.refl _,Nat.le_add_right _ _⟩
  | cons l ls ih =>
    have h:=ih (cappedStep (l,z))
    dsimp only at h ⊢
    simp only [List.foldl_cons]
    refine ⟨h.1,h.2.1.trans (Nat.sub_le _ _),h.2.2.1.trans (List.filter_sublist (p:=fun b=>!(totalFlag (l,b))) (l:=z.2.2.1)),?_⟩

    cases ls with
    | nil =>
      change weight (cappedUpdate _)≤_
      exact (cappedUpdate_weight _).trans (Nat.le_add_left _ _)
    | cons l' ls =>

      clear ih h
      have hs : ∀ (as : List ℕ) (v : CappedState) (j : ℕ),
          weight ((as.foldl (fun z l=>cappedStep (l,z)) (cappedStep (j,v))).2.2.2)≤tableWeightBound v.1 := by
        intro as
        induction as with
        | nil => intro v j; exact cappedUpdate_weight _
        | cons a as ih =>
          intro v j
          simp only [List.foldl_cons]
          exact ih (cappedStep (j,v)) a
      exact (hs ls (cappedStep (l,z)) l').trans (Nat.le_add_left _ _)

lemma weight_cappedState (z : CappedState) : weight z=3+weight z.1+weight z.2.1+weight z.2.2.1+weight z.2.2.2 := by
  rcases z with ⟨o,k,bs,t⟩
  simp only [weight_prod]
  omega

lemma polynomial_cappedFold : PolynomialTime (fold cappedStepRealizer) := by
  let P : Polynomial ℕ := 1+X*(2+(X^2+1)*(4*(X^2+X^5+1)+2))
  apply polynomial_fold polynomial_cappedStep (8*X+10+P)
  intro ls z pre _ _
  let S:=weight (ls,z)
  let r:=pre.foldl (fun z l=>cappedStep (l,z)) z
  have hi:=cappedFold_invariant pre z
  change r.1=z.1 ∧ r.2.1≤z.2.1 ∧ r.2.2.1.Sublist z.2.2.1 ∧ weight r.2.2.2≤weight z.2.2.2+tableWeightBound z.1 at hi
  have hz : weight z≤S := weight_snd (ls,z)
  have ho : weight z.1≤S := (weight_fst z).trans hz
  have hr : weight z.2.1≤S := (weight_fst z.2).trans ((weight_snd z).trans hz)
  have hb : weight z.2.2.1≤S := (weight_fst z.2.2).trans ((weight_snd z.2).trans ((weight_snd z).trans hz))
  have ht : weight z.2.2.2≤S := (weight_snd z.2.2).trans ((weight_snd z.2).trans ((weight_snd z).trans hz))
  have h0 : weight r.1≤S := by rw [hi.1]; exact ho
  have h1 : weight r.2.1≤4*S+1 := by
    have hh:=weight_nat_le r.2.1
    have hh':=(Nat.size_le_size hi.2.1).trans (size_le_weight z.2.1)
    omega
  have h2 : weight r.2.2.1≤S := (weight_sublist hi.2.2.1).trans hb
  have htable:tableWeightBound z.1≤P.eval S := by
    apply (tableWeightBound_polynomial z.1).trans
    simpa only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X] using polynomial_eval_monotone P ho
  change weight r≤_
  rw [weight_cappedState r]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤8*S+10+P.eval S
  omega

def finishFast : Realizer (fun x : CountInput×Table=>finish (x.2,nLabels x.1)) :=
  composition (composition (pair second (composition (composition first nLabelsRealizer) range))
    (mapWith (composition (pair first (pair second (constant 0))) readFast))) listProd
lemma polynomial_finishFast : PolynomialTime finishFast := by
  unfold finishFast
  apply polynomial_composition _ polynomial_listProd
  apply polynomial_composition
  · apply polynomial_pair polynomial_second
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_nLabels) X
    intro x
    simp only [Function.comp_apply,Polynomial.eval_X]
    exact (input_lengths x.1).2.1.trans (weight_fst x)
  · apply polynomial_mapWith
    apply polynomial_composition _ polynomial_readFast
    tree_poly

def cappedCount (o : CountInput) : ℕ :=
  finish ((o.2.foldl (fun z l=>cappedStep (l,z)) (o,(o.2.length,(o.1.1,initial (nLabels o,BInitial o))))).2.2.2,nLabels o)
def cappedCountRealizer : Realizer cappedCount := by
  let init : Realizer (fun o : CountInput=>(o.2,(o,(o.2.length,(o.1.1,initial (nLabels o,BInitial o)))))) :=
    pair second (pair identity (pair nPlanRealizer (pair first.fst initialFast)))
  exact (composition (pair identity (composition (composition init (fold cappedStepRealizer)) second.snd.snd)) finishFast).congr (fun _=>rfl)
lemma polynomial_cappedCount : PolynomialTime cappedCountRealizer := by
  unfold cappedCountRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_finishFast
  apply polynomial_pair polynomial_identity
  apply polynomial_composition _ (polynomial_snd (polynomial_snd polynomial_second))
  apply polynomial_composition _ polynomial_cappedFold
  apply polynomial_pair polynomial_second
  apply polynomial_pair polynomial_identity
  apply polynomial_pair polynomial_nPlan
  exact polynomial_pair (polynomial_fst polynomial_first) polynomial_initialFast
end MatchingFPRAS.ExecutableDP

end OAI
