import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.EventMass

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def hits {n : ℕ} (H : Finset α) (x : Fin n → α) : ℝ :=
  ∑ i,if x i∈H then 1 else 0

omit [Fintype α] in
lemma hits_cons (H : Finset α) {n : ℕ} (a : α) (x : Fin n → α) :
    hits H (Fin.cons a x)=(if a∈H then 1 else 0)+hits H x := by
  simp only [hits,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma expected_hits (p : Law α) (H : Finset α) (n : ℕ) :
    (∑ x,iid p (Fin n) x*hits H x)=(n:ℝ)*eventMass p H := by
  induction n with
  | zero => simp [hits]
  | succ n hn =>
    rw [sum_iid_succ]
    simp only [hits_cons,mul_add,Finset.sum_add_distrib]
    have h1 : (∑ a,∑ x,p a*iid p (Fin n) x*(if a∈H then 1 else 0))=eventMass p H := by
      calc
        _ = ∑ a,p a*(if a∈H then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [←Finset.sum_mul,←Finset.mul_sum,(iid p (Fin n)).sum_one,mul_one]
        _ = _ := by simp [mul_ite,eventMass]
    have h2 : (∑ a,∑ x,p a*iid p (Fin n) x*hits H x)=(n:ℝ)*eventMass p H := by
      simp only [mul_assoc,←Finset.mul_sum,hn,←Finset.sum_mul,p.sum_one,one_mul]
    rw [h1,h2,Nat.cast_add,Nat.cast_one]
    ring

lemma event_markov (p : Law α) (w : α → ℝ) (hw : ∀ a,0≤w a) (t : ℝ)
    (E : Finset α) (hE : ∀ a∈E,t≤w a) :
    t*eventMass p E≤∑ a,p a*w a := by
  rw [eventMass,Finset.mul_sum]
  calc
    _ ≤ ∑ a∈E,p a*w a := Finset.sum_le_sum fun a ha => by
      simpa only [mul_comm t] using mul_le_mul_of_nonneg_left (hE a ha) (p.nonneg a)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
      mul_nonneg (p.nonneg a) (hw a))

theorem iid_test_rejection (p : Law α) (H : Finset α) (n : ℕ) (hn : 0<n)
    (c : ℝ) (hc : 0<c) :
    eventMass (iid p (Fin n)) (Finset.univ.filter fun x => c*n≤hits H x)≤eventMass p H/c := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hh := event_markov (iid p (Fin n)) (hits H) (by
      intro x
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num)
    (c*n) (Finset.univ.filter fun x => c*n≤hits H x) (by
      intro x hx
      exact (Finset.mem_filter.mp hx).2)
  rw [expected_hits] at hh
  apply (le_div_iff₀ hc).mpr
  nlinarith

lemma first_success_atom_le (p : Law α) (E : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a)≤p a/eventMass p E := by
  let r := map (iid p (Fin n)) (firstAccepted E (n := n))
  have hd := first_success_density p E n hn hE a
  have hs : 0<1-r none := by
    dsimp [r]
    rw [first_law_none]
    have hq : 0≤1-eventMass p E := sub_nonneg.mpr (eventMass_le_one p E)
    have hq1 : 1-eventMass p E<1 := by linarith
    have hp := pow_lt_one₀ hq hq1 (Nat.ne_of_gt hn)
    linarith
  change r (some a)/(1-r none)≤p a/eventMass p E at hd
  have hd' := (div_le_iff₀ hs).mp hd
  have hn0 := r.nonneg none
  have hpa : 0≤p a/eventMass p E := div_nonneg (p.nonneg a) hE.le
  change r (some a)≤_
  nlinarith

theorem first_success_bad_mass (p : Law α) (E Bad : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) :
    eventMass (map (iid p (Fin n)) (firstAccepted E (n := n))) (Bad.image some)≤
      eventMass p Bad/eventMass p E := by
  classical
  rw [eventMass,Finset.sum_image (by intro a _ b _ h; exact Option.some.inj h)]
  calc
    _ ≤ ∑ a∈Bad,p a/eventMass p E := Finset.sum_le_sum fun a _ =>
      first_success_atom_le p E n hn hE a
    _ = _ := by rw [←Finset.sum_div]; rfl

end
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def uniformOn (A : Finset α) (hA : A.Nonempty) : Law α where
  mass a := if a∈A then (A.card:ℝ)⁻¹ else 0
  nonneg a := by split_ifs <;> positivity
  sum_one := by
    have hc : (A.card:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hA)
    rw [←Finset.sum_filter,Finset.filter_univ_mem,Finset.sum_const,nsmul_eq_mul,mul_inv_cancel₀ hc]

lemma uniformOn_mass (A : Finset α) (hA : A.Nonempty) (H : Finset α) :
    eventMass (uniformOn A hA) H = ((H∩A).card:ℝ)/A.card := by
  simp only [eventMass,uniformOn,←Finset.sum_filter,Finset.filter_mem_eq_inter,
    Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

lemma iid_uniformOn {n : ℕ} (A : Finset α) (hA : A.Nonempty) (x : Fin n → α) :
    iid (uniformOn A hA) (Fin n) x =
      if (∀ i,x i∈A) then ((A.card:ℝ)⁻¹)^n else 0 := by
  by_cases h : ∀ i,x i∈A
  · simp [iid,uniformOn,h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [iid]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [uniformOn,hi])]
    simp only [h,ite_false]

lemma uniformOn_row_scaling {n : ℕ} (A W : Finset α) (hA : A.Nonempty)
    (hW : W.Nonempty) (hAW : A⊆W) (x : Fin n → α) (hx : ∀ i,x i∈A) :
    iid (uniformOn W hW) (Fin n) x = ((A.card:ℝ)/W.card)^n*
      iid (uniformOn A hA) (Fin n) x := by
  rw [iid_uniformOn,iid_uniformOn,ite_eq_left hx,ite_eq_left (fun i => hAW (hx i))]
  have hc : (A.card:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hA)
  rw [←mul_pow]
  congr 1
  field_simp

lemma eventMass_scaling (p r : Law α) (E : Finset α) (s : ℝ)
    (h : ∀ a∈E,p a=s*r a) : eventMass p E=s*eventMass r E := by
  simp only [eventMass,Finset.mul_sum]
  exact Finset.sum_congr rfl h

theorem first_success_scaled (p r : Law α) (E : Finset α) (s : ℝ) (hs : 0<s)
    (hscale : ∀ a∈E,p a=s*r a) (N : ℕ) (hN : 0<N)
    (hE : 0<eventMass r E) (a : α) :
    map (iid p (Fin N)) (firstAccepted E (n := N)) (some a) ≤ r a/eventMass r E := by
  by_cases ha : a∈E
  · have he := eventMass_scaling p r E s hscale
    have hpE : 0<eventMass p E := by rw [he]; exact mul_pos hs hE
    have hh := first_success_atom_le p E N hN hpE a
    rw [he,hscale a ha] at hh
    have heq : s*r a/(s*eventMass r E)=r a/eventMass r E := by field_simp
    rwa [heq] at hh
  · rw [first_law_some]
    simp only [ha,ite_false,zero_mul]
    exact div_nonneg (r.nonneg a) hE.le

lemma first_success_scaled_bad (p r : Law α) (E Bad : Finset α) (s : ℝ) (hs : 0<s)
    (hscale : ∀ a∈E,p a=s*r a) (N : ℕ) (hN : 0<N) (hE : 0<eventMass r E) :
    eventMass (map (iid p (Fin N)) (firstAccepted E (n := N))) (Bad.image some) ≤
      eventMass r Bad/eventMass r E := by
  rw [eventMass,Finset.sum_image (by intro a _ b _ h; exact Option.some.inj h)]
  calc
    _ ≤ ∑ a∈Bad,r a/eventMass r E := Finset.sum_le_sum fun a _ =>
      first_success_scaled p r E s hs hscale N hN hE a
    _ = _ := by rw [←Finset.sum_div]; rfl

theorem uniform_proposal_bad (A W : Finset α) (hA : A.Nonempty) (hW : W.Nonempty)
    (hAW : A⊆W) (h N : ℕ) (hN : 0<N) (E Bad : Finset (Fin h → α))
    (hsource : ∀ x∈E,∀ i,x i∈A) (hE : 0<eventMass (iid (uniformOn A hA) (Fin h)) E) :
    eventMass (map (iid (iid (uniformOn W hW) (Fin h)) (Fin N))
      (firstAccepted E (n := N))) (Bad.image some) ≤
      eventMass (iid (uniformOn A hA) (Fin h)) Bad /
        eventMass (iid (uniformOn A hA) (Fin h)) E := by
  have hcA : (0:ℝ)<A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hcW : (0:ℝ)<W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hh := first_success_scaled_bad _ _ E Bad (((A.card:ℝ)/W.card)^h) (by positivity)
    (fun x hx => uniformOn_row_scaling A W hA hW hAW x (hsource x hx)) N hN hE
  convert hh using 1
  congr 1
  ext x
  simp only [Finset.mem_image]

end SharpRamseyFive.FiniteEntropy

end OAI
