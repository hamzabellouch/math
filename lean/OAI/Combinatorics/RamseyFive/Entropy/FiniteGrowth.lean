import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.EventMass
import OAI.Combinatorics.RamseyFive.Entropy.EventWeight

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {S A : Type*}

def runSamples (step : S→A→S) : S→{n : ℕ}→(Fin n→A)→S
  | s,0,_=>s
  | s,_+1,x=>runSamples step (step s (x 0)) (fun i=>x i.succ)

def failedGrowth (step : S→A→S) (rank : S→ℕ) (d : ℕ) (s : S) (a : A) : Prop :=
  rank s<d ∧ rank (step s a)≤rank s

def growthFailures (step : S→A→S) (rank : S→ℕ) (d : ℕ) : S→{n : ℕ}→(Fin n→A)→ℕ
  | _,0,_=>0
  | s,_+1,x=>(if failedGrowth step rank d s (x 0) then 1 else 0)+
      growthFailures step rank d (step s (x 0)) (fun i=>x i.succ)

lemma runSamples_cons (step : S→A→S) (s : S) {n : ℕ} (a : A) (x : Fin n→A) :
    runSamples step s (Fin.cons a x)=runSamples step (step s a) x := by
  simp only [runSamples,Fin.cons_zero,Fin.cons_succ]

lemma growthFailures_cons (step : S→A→S) (rank : S→ℕ) (d : ℕ) (s : S)
    {n : ℕ} (a : A) (x : Fin n→A) :
    growthFailures step rank d s (Fin.cons a x)=
      (if failedGrowth step rank d s a then 1 else 0)+growthFailures step rank d (step s a) x := by
  simp only [growthFailures,Fin.cons_zero,Fin.cons_succ]

lemma runSamples_rank_mono (step : S→A→S) (rank : S→ℕ)
    (hmono : ∀ s a,rank s≤rank (step s a)) (s : S) {n : ℕ} (x : Fin n→A) :
    rank s≤rank (runSamples step s x) := by
  induction n generalizing s with
  | zero=>exact le_rfl
  | succ n ih=>exact (hmono _ _).trans (ih _ _)

lemma zero_growthFailures (step : S→A→S) (rank : S→ℕ) (d : ℕ)
    (hmono : ∀ s a,rank s≤rank (step s a)) (s : S) {n : ℕ} (x : Fin n→A)
    (h : growthFailures step rank d s x=0) :
    min d (rank s+n)≤rank (runSamples step s x) := by
  induction n generalizing s with
  | zero=>simpa only [Nat.add_zero,runSamples] using Nat.min_le_right d (rank s)
  | succ n ih=>
    have hn : ¬failedGrowth step rank d s (x 0) := by
      intro hn
      simp only [growthFailures,hn,ite_true] at h
      omega
    have ht : growthFailures step rank d (step s (x 0)) (fun i=>x i.succ)=0 := by
      simpa only [growthFailures,hn,ite_false,Nat.zero_add] using h
    have hh:=ih (step s (x 0)) (fun i=>x i.succ) ht
    have hm:=hmono s (x 0)
    have hm':=runSamples_rank_mono step rank hmono (step s (x 0)) (fun i=>x i.succ)
    change min d (rank s+(n+1))≤rank (runSamples step (step s (x 0)) (fun i=>x i.succ))
    unfold failedGrowth at hn
    omega

variable [Fintype A]

theorem growthFailures_mean (p : Law A) (step : S→A→S) (rank : S→ℕ) (d : ℕ)
    (e : ℝ) (hstep : ∀ s,eventWeight p (failedGrowth step rank d s)≤e)
    (s : S) (n : ℕ) :
    (∑ x,iid p (Fin n) x*(growthFailures step rank d s x:ℝ))≤n*e := by
  induction n generalizing s with
  | zero=>simp [growthFailures]
  | succ n ih=>
    rw [sum_iid_succ]
    have he : (∑ a,∑ x,p a*iid p (Fin n) x*
        (growthFailures step rank d s (Fin.cons a x):ℝ))=
        eventWeight p (failedGrowth step rank d s)+
        ∑ a,p a*(∑ x,iid p (Fin n) x*(growthFailures step rank d (step s a) x:ℝ)) := by
      simp only [growthFailures_cons,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
        mul_add,Finset.sum_add_distrib,eventWeight]
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        rw [←Finset.sum_mul,←Finset.mul_sum,(iid p (Fin n)).sum_one,mul_one]
        simp only [mul_ite,mul_one,mul_zero]
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    rw [he]
    calc
      _ ≤ e+∑ a,p a*(n*e) := add_le_add (hstep s)
        (Finset.sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (ih _) (p.nonneg a))
      _ = _ := by rw [←Finset.sum_mul,p.sum_one]; push_cast; ring

theorem iid_growth_failure (p : Law A) (step : S→A→S) (rank : S→ℕ) (d : ℕ)
    (hmono : ∀ s a,rank s≤rank (step s a)) (e : ℝ)
    (hstep : ∀ s,eventWeight p (failedGrowth step rank d s)≤e)
    (s : S) (n : ℕ) (hstart : d≤rank s+n) :
    eventWeight (iid p (Fin n)) (fun x=>rank (runSamples step s x)<d)≤n*e := by
  apply le_trans _ (growthFailures_mean p step rank d e hstep s n)
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · have hp : 0<growthFailures step rank d s x := by
      by_contra hh
      have hz : growthFailures step rank d s x=0 := by omega
      have hb:=zero_growthFailures step rank d hmono s x hz
      omega
    exact le_mul_of_one_le_right ((iid p (Fin n)).nonneg x) (by exact_mod_cast hp)
  · exact mul_nonneg ((iid p (Fin n)).nonneg x) (Nat.cast_nonneg _)
end

noncomputable section
variable {A : Type*}

lemma firstAccepted_none_iff (E : Finset A) {n : ℕ} (x : Fin n→A) :
    firstAccepted E x=none ↔ ∀ i,x i∉E := by
  induction n with
  | zero=>simp [firstAccepted]
  | succ n ih=>
    rw [firstAccepted]
    split_ifs with h
    · simp only [false_iff,not_forall]
      exact ⟨0,by simpa using h⟩
    · rw [ih]
      constructor
      · intro hh i
        refine Fin.cases ?_ (fun j=>hh j) i
        exact h
      · intro hh i
        exact hh i.succ

variable [Fintype A]

lemma iid_avoidance (p : Law A) (E : Finset A) (n : ℕ) :
    eventWeight (iid p (Fin n)) (fun x=>∀ i,x i∉E)=(1-eventMass p E)^n := by
  rw [←first_law_none p E n]
  unfold eventWeight map
  apply Finset.sum_congr rfl
  intro x _
  rw [firstAccepted_none_iff]

lemma eventWeight_mono (p : Law A) (P Q : A→Prop) (h : ∀ a,P a→Q a) :
    eventWeight p P≤eventWeight p Q := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a
  · simp only [hp,h a hp,ite_true,le_refl]
  · simp only [hp,ite_false]
    split_ifs <;> first | exact p.nonneg a | exact le_rfl

lemma eventWeight_union (p : Law A) (P Q : A→Prop) :
    eventWeight p (fun a=>P a ∨ Q a)≤eventWeight p P+eventWeight p Q := by
  unfold eventWeight
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;>
    simp only [hp,hq,true_or,false_or,or_false,ite_true,ite_false,zero_add,add_zero,le_refl]
  exact le_add_of_nonneg_right (p.nonneg a)
end
end SharpRamseyFive.FiniteEntropy

end OAI
