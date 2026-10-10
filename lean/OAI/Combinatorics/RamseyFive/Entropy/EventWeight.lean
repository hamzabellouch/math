import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SubsetMixture
import OAI.Combinatorics.RamseyFive.Marking.ReverseMiss

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]
noncomputable def eventWeight (p : Law α) (E : α → Prop) : ℝ :=
  ∑ a,if E a then p a else 0
lemma eventWeight_nonneg (p : Law α) (E : α → Prop) : 0≤eventWeight p E := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact p.nonneg a
  · exact le_rfl
lemma eventWeight_comparison (p q : Law α) (h : ∀ a,0<p a → 0<q a) (E : α → Prop) :
    eventWeight q E≤2*(divergence p q+eventWeight p E) := by
  simpa only [Finset.sum_filter,eventWeight] using
    event_comparison p q h (Finset.univ.filter E)
lemma eventWeight_zero (p : Law α) (E : α → Prop) (h : ∀ a,E a → p a=0) :
    eventWeight p E=0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with he
  · exact h a he
  · rfl
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma crossed_eventWeight (p : Law (α × β)) (q : Law (γ × δ))
    (E : α → β → γ → δ → Prop) :
    eventWeight (product p q) (fun z => E z.1.1 z.1.2 z.2.1 z.2.2)=
      ∑ a,∑ y,(first p a*second q y)*
        (∑ b,∑ c,if E a b c y then fiber p a b*fiber (swap q) y c else 0) := by
  have h := product_crossed_expectation p q (fun a b c y => if E a b c y then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,eventWeight] using h

lemma crossed_endpoint (p : Law (α × β)) (q : Law (γ × δ)) (good : α → δ → Prop) :
    eventWeight (product p q) (fun z => good z.1.1 z.2.2)=
      ∑ a,∑ y,(first p a*second q y)*(if good a y then 1 else 0) := by
  rw [crossed_eventWeight p q (fun a _ _ y => good a y)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : good a y
  · simp only [h,ite_true,←Finset.mul_sum,(fiber (swap q) y).sum_one,mul_one,
      (fiber p a).sum_one]
  · simp only [h,ite_false,Finset.sum_const_zero,mul_zero]

lemma crossed_conflict (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop) :
    eventWeight (product p q) (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)=
      ∑ a,∑ y,(first p a*second q y)*
        (if good a y then reverseMiss (fiber p a) (fiber (swap q) y) v w else 0) := by
  rw [crossed_eventWeight p q (fun a b c y => good a y ∧ v b (w c)≠0)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : good a y
  · simp only [h,true_and,ite_true,reverseMiss]
  · simp only [h,false_and,ite_false,Finset.sum_const_zero]

theorem integrated_charge [FiniteDimensional K V] (hdim : finrank K V=5)
    (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop) :
    (19/20:ℝ)*eventWeight (product p q) (fun z => good z.1.1 z.2.2)≤
      38000*eventWeight (product p q) (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)+
      eventWeight (product p q) (fun z => capturedEvent p q v w good z.1.1 z.1.2 z.2.1 z.2.2) := by
  rw [crossed_endpoint,crossed_conflict,crossed_eventWeight]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  have h := mul_le_mul_of_nonneg_left (conditional_charge hdim p q v w good a y)
    (mul_nonneg ((first p).nonneg a) ((second q).nonneg y))
  nlinarith

theorem low_conflict_bound [FiniteDimensional K V] (hdim : finrank K V=5)
    (p : Law ((α × β) × (γ × δ)))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop)
    (hconsistent : ∀ z,0<p z → good z.1.1 z.2.2 → v z.1.2 (w z.2.1)=0) :
    eventWeight (product (first p) (second p)) (fun z => good z.1.1 z.2.2)≤
      80004*(entropy (first p)+entropy (second p)-entropy p+
        eventWeight p (fun z => capturedEvent (first p) (second p) v w good
          z.1.1 z.1.2 z.2.1 z.2.2)) := by
  have hz : eventWeight p (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)=0 := by
    apply eventWeight_zero
    intro z hz
    apply le_antisymm _ (p.nonneg z)
    by_contra h
    exact hz.2 (hconsistent z (lt_of_not_ge h) hz.1)
  have hc := eventWeight_comparison p (product (first p) (second p)) (ac_product p)
    (fun z => good z.1.1 z.2.2 ∧ v z.1.2 (w z.2.1)≠0)
  rw [hz,add_zero,mutual_information] at hc
  have he := eventWeight_comparison p (product (first p) (second p)) (ac_product p)
    (fun z => capturedEvent (first p) (second p) v w good z.1.1 z.1.2 z.2.1 z.2.2)
  rw [mutual_information] at he
  have hi := entropy_subadditive p
  have hcap := eventWeight_nonneg p
    (fun z => capturedEvent (first p) (second p) v w good z.1.1 z.1.2 z.2.1 z.2.2)
  have h := integrated_charge hdim (first p) (second p) v w good
  linarith
end SharpRamseyFive.LowConflict

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma good_mixture_zero (μ : Law (Finset α)) (G : Finset α)
    (hG : ∀A,0<μ A→A⊆G) {a : α} (ha : a∉G) :
    (∑A,μ A*uniformWeight A a)=0 := by
  apply Finset.sum_eq_zero
  intro A _
  by_cases hm : μ A=0
  · simp [hm]
  have hp : 0<μ A := lt_of_le_of_ne (μ.nonneg A) (Ne.symm hm)
  have ht : a∉A := fun hh=>ha (hG A hp hh)
  simp [uniformWeight,ht]

theorem independent_good_subset_domination (R : α→β→Prop)
    (p : Law α) (r : Law β) (GA : Finset α) (GB : Finset β)
    (μ : Law (Finset α)) (ν : Law (Finset β)) (L : ℝ) (hL : 0≤L)
    (hGA : ∀A,0<μ A→A⊆GA) (hGB : ∀B,0<ν B→B⊆GB)
    (hμ : ∀a,(∑A,μ A*uniformWeight A a)≤L*p a)
    (hν : ∀b,(∑B,ν B*uniformWeight B b)≤L*r b) :
    (∑A,∑B,μ A*ν B*relationMass R (uniformWeight A) (uniformWeight B))≤
      L^2*relationMass (fun a b=>a∈GA ∧ b∈GB ∧ R a b) p r := by
  rw [independent_subset_relation]
  unfold relationMass
  simp only [Finset.sum_filter]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases ha : z.1∈GA
  · by_cases hb : z.2∈GB
    · by_cases hR : R z.1 z.2
      · simp only [ha,hb,hR,and_self,↓reduceIte]
        have hn : 0≤∑B,ν B*uniformWeight B z.2 := Finset.sum_nonneg
          (fun B _=>mul_nonneg (ν.nonneg B) (uniformWeight_nonneg B z.2))
        have hh := mul_le_mul (hμ z.1) (hν z.2) hn (mul_nonneg hL (p.nonneg z.1))
        nlinarith only [hh]
      · simp [hR]
    · rw [good_mixture_zero ν GB hGB hb]
      simp [hb]
  · rw [good_mixture_zero μ GA hGA ha]
    simp [ha]

end SharpRamseyFive.FiniteEntropy

end OAI
