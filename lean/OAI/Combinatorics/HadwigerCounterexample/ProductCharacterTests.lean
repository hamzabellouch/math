import OAI.Combinatorics.HadwigerCounterexample.ConditionedCorrelations

namespace OAI

/-! # Product Character Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators
variable {I J A Z D : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable [Fintype A]

def Pipe (P : A→Z→ ℝ) :=
  ∃ (f : A→ℝ) (g : Z→ℝ),(∀ i, |f i|≤1) ∧ (∀ i, |g i|≤1) ∧ ∀ x y,P x y=f x*g y

omit [Fintype I] [Fintype A] in
private theorem pipe_prod (s : Finset I) (P : I → A→Z→ℝ)
    (h : ∀ i∈s,Pipe (P i)) :
    Pipe (fun x y => ∏ i∈s,P i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ =>1,fun _=>1,(by simp),(by simp),fun _ _=>by simp⟩
  | @insert i s hi ih =>
    obtain ⟨f,g,hf,hg,hH⟩ := h i (by simp)
    obtain ⟨u,v,hu,hv,hU⟩ := ih (fun j hj => h j (mem_insert_of_mem hj))
    have he (f g : ℝ) (hf : |f|≤1) (hg : |g|≤1) :
        |f*g|≤1 := by rw [abs_mul]; exact (mul_le_mul hf hg (abs_nonneg _) zero_le_one).trans_eq
                                            (by ring)
    exact ⟨fun x => f x*u x,fun x => g x*v x,(fun x=>he _ _ (hf x) (hu x)),
      (fun x => he _ _ (hg x) (hv x)),fun x y => by dsimp only at *; rw [prod_insert hi,hH,hU]; ring⟩

structure Stage (I J : Type) where
  first : J→I
  nextP : J→I
  diff k : first k ≠ nextP k
  once k j : first k=first j → nextP k=nextP j → k=j
  anti k j : first k=nextP j → nextP k≠first j

variable (s : Stage I J)

set_option maxHeartbeats 600000 in
theorem far_avg (w : I→Wgt A) (hw : ∀ i,IsLaw (w i)) (F : Wgt (I→A)) (i j : I)
    (_ : i ≠ j) :
    let U := prodW w
    avg U F = avg U (fun x => avg (pairW (w i) (w j)) (fun y => F (update (update x i y.1) j y.2))) := by
  classical
  intro U
  rw [update_avg w j F (hw j),update_avg w i _ (hw i)]
  simp only [U,pairW_avg]
private def moveInputs (i j : I) (x : I→A) (p q : A) := update (update x i p) j q

set_option maxHeartbeats 800000 in
theorem band_res (w : I→ Wgt A) (hw : ∀ i,IsLaw (w i))
    (f : I→ Wgt A) (hf : ∀ i x,|f i x|≤1)
    (u : J→ A→ A→ℝ) (hu : ∀ k x y,|u k x y|≤1)
    (k : J) (η : ℝ)
    (h : ∀ p q : Wgt A,(∀ i, |p i|≤1)→(∀ i,|q i|≤1) →
      |avg (pairW (w (s.first k)) (w (s.nextP k))) (fun x =>
        u k x.1 x.2 * (p x.1*q x.2))|≤η) :
    |avg (prodW w) (fun x => (∏ j:J,u j (x (s.first j)) (x (s.nextP j)))*prodW f x)|≤η := by
  classical
  let i:=s.first k; let j:=s.nextP k
  have hj : i≠ j := s.diff k
  let W (x : I→ A) := (∏ j':J,u j' (x (s.first j')) (x (s.nextP j')))*prodW f x
  have hi (z : I→A) :
      |avg (pairW (w i) (w j)) (fun x => W (moveInputs i j z x.1 x.2))|≤ η := by
    let C a b := moveInputs i j z a b
    let g (v : J⊕I) (a b : A) :=
      match v with
      | .inl t => if t=k then 1 else u t (C a b (s.first t)) (C a b (s.nextP t))
      | .inr t => f t (C a b t)
    have he a b :
        W (C a b)=u k a b * ∏ l:J ⊕ I,g l a b := by
      unfold W prodW; rw [Fintype.prod_sum_type]
      rw [← mul_prod_erase _ _ (mem_univ k),←mul_prod_erase _
        (fun t:J=>g (.inl t) a b) (mem_univ k)]
      have he (t:J) (h : t∈univ.erase k) :
          g (Sum.inl t) a b=u t (C a b (s.first t)) (C a b (s.nextP t)) :=
        ite_eq_right (mem_erase.mp h).1
      rw [Finset.prod_congr rfl (g:=fun t:J => u t (C a b (s.first t)) (C a b (s.nextP t))) he]
      change (u k (C a b i) (C a b j)*_) *_=_
      rw [show C a b i=a from (by simp [C,moveInputs,hj]),
        show C a b j=b from (by simp [C,moveInputs]),show g (.inl k) a b=1 from
        (by simp [g]),one_mul,mul_assoc]
    let d := z i
    have hp : ∀ x:J ⊕ I,Pipe (g x) := by
      have he (t : I) (h : t ≠ j) (a b : A) : C a b t=C a d t := by
        unfold C moveInputs; rw [update_of_ne h,update_of_ne h]
      have hu' (t : I) (h : t ≠ i) (a b : A) : C a b t=C d b t := by
        unfold C moveInputs
        by_cases hx : t=j <;> simp [hx,h]
      have h1 (x:J⊕I) (h : ∀ a b,|g x a b|≤1)
          (e : (∀ a b,g x a b=g x a d)∨(∀ a b,g x a b=g x d b)) :
          Pipe (g x) := by
        rcases e with e|e
        · exact ⟨fun a=>g x a d,fun _=>1,fun i=>h _ _,(by simp),fun i j=> (e i j).trans
            (by rw [mul_one])⟩
        exact ⟨fun _=>1,g x d,(by simp),h d,fun i j=> (e i j).trans (by rw [one_mul])⟩
      rintro (l|l)
      · by_cases hh : l=k
        · subst l; exact h1 (Sum.inl k) (by simp [g]) (Or.inl (by simp [g]))
        apply h1 (Sum.inl l) (fun a b => by simp only [g,ite_eq_right hh]; exact hu _ _ _)
        have hh1 :
            (s.first l≠j∧s.nextP l≠j) ∨(s.first l≠i∧s.nextP l≠i) := by
          by_contra! ha
          by_cases hx : s.first l=j
          · have hy : s.first l≠i := hx ▸ Ne.symm hj
            exact s.anti l k hx (ha.2 hy)
          have ht := ha.1 hx
          have hs : s.first l=i := by_contra (fun h=>hj ((ha.2 h).symm.trans ht))
          exact hh (s.once l k hs ht)
        simp only [g,ite_eq_right hh]; rcases hh1 with ⟨h,h'⟩|⟨h,h'⟩
        · left; intro a b; rw [he _ h,he _ h']
        right; intro a b; rw [hu' _ h,hu' _ h']
      apply h1 (Sum.inr l) (fun a b => hf _ _)
      unfold g
      by_cases h : l=i
      · exact Or.inl fun a b => congrArg _ (he _ (h.symm ▸ hj) _ _)
      exact Or.inr fun a b=> congrArg _ (hu' l h a b)
    obtain ⟨p,q,hp,hq,ht⟩ := pipe_prod univ g (fun i _ => hp i)
    have heq (x : A×A) : W (moveInputs i j z x.1 x.2)=u k x.1 x.2*(p x.1*q x.2) := by
      change W (C _ _)=_
      rw [he]; exact congrArg (_ * ·) (ht x.1 x.2)
    simp_rw [heq]
    exact h p q hp hq
  change |avg _ W|≤η
  rw [far_avg w hw W i j hj]
  exact (abs_avg_le (prodW_law hw).nz).trans ((prodW_law hw).avg_le hi)
end HadwigerCounterexample

end

end OAI
