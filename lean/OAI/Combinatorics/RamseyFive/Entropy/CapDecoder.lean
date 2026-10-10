import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.FreshValidation

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}

lemma firstAccepted_index {n : ℕ} (E : Finset A) (t : Fin n→A) {a : A}
    (ha : firstAccepted E t=some a) : ∃i,t i=a ∧ a∈E := by
  induction n with
  | zero => simp [firstAccepted] at ha
  | succ n ih =>
    rw [firstAccepted] at ha
    split_ifs at ha with h
    · have he := Option.some.inj ha
      exact ⟨0,he,he ▸ h⟩
    · obtain ⟨i,hi,hm⟩ := ih _ ha
      exact ⟨i.succ,hi,hm⟩

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

lemma cap_subset (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    cap R U q row⊆U := Finset.filter_subset _ _

theorem validation_decode (R : A→B→Prop) (S U : Finset A) (C : Finset B)
    (n N : ℕ) (q M : ℝ) (t : Fin N→Fin n→B) (row : Fin n→B)
    (hrow : firstAccepted (validationRows R S U C n q M) t=some row) :
    ∃i : Fin N, cap R U q (t i)⊆U ∧
      ((cap R U q (t i)).card:ℝ) ≤ M ∧
      (9:ℝ)/10*S.card ≤ (S∩cap R U q (t i)).card := by
  obtain ⟨i,hi,hm⟩ := firstAccepted_index _ _ hrow
  refine ⟨i,cap_subset _ _ _ _,?_⟩
  rw [hi]
  exact (Finset.mem_filter.mp hm).2.2

theorem reverse_decode (R : A→B→Prop) (S U : Finset A) (hSU : S⊆U)
    (C : Finset B) (n N : ℕ) (hn : 0 < n) (q κ M : ℝ) (hq : 0 < q)
    (hC : ∀b∈C,((S.filter fun a=>R a b).card:ℝ) ≤ κ*S.card)
    (t : Fin N→Fin n→B) (row : Fin n→B)
    (hrow : firstAccepted (successfulRows R U C n q M) t=some row) :
    ∃i : Fin N, cap R U q (t i)⊆U ∧
      ((cap R U q (t i)).card:ℝ) ≤ M ∧
      (1-5*q*κ)*S.card ≤ (S∩cap R U q (t i)).card := by
  obtain ⟨i,hi,hm⟩ := firstAccepted_index _ _ hrow
  refine ⟨i,cap_subset _ _ _ _,?_⟩
  rw [hi]
  have hh := (Finset.mem_filter.mp hm).2
  exact ⟨hh.2,deterministic_capture R S U hSU C hn q κ hq hC row hh.1⟩

end SharpRamseyFive.ReverseCap

end

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma uniform_source_fraction (A X H : Finset α) (hA : A.Nonempty) (hAX : A⊆X)
    (c : ℝ) (hc : 0<c) (hsize : c*X.card≤A.card) :
    eventMass (uniformOn A hA) H≤((H∩X).card:ℝ)/(c*X.card) := by
  have hX : X.Nonempty := hA.mono hAX
  have hnA : (0:ℝ)<A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hnX : (0:ℝ)<X.card := by exact_mod_cast Finset.card_pos.mpr hX
  have hcard : ((H∩A).card:ℝ)≤(H∩X).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl H) hAX)
  rw [uniformOn_mass]
  exact div_le_div₀ (by positivity) hcard (by positivity) hsize

theorem fresh_test_domination (A X W H : Finset α) (hA : A.Nonempty) (hW : W.Nonempty)
    (hAW : A⊆W) (hAX : A⊆X) (q c : ℝ) (hq : 0<q) (hc : 0<c)
    (hsize : c*X.card≤A.card) (h N : ℕ) (hh : 0<h) (hN : 0<N)
    (E : Finset (Fin h → α)) (hsource : ∀ x∈E,∀ i,x i∈A)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn A hA) (Fin h)) E) :
    eventMass (map (iid (iid (uniformOn W hW) (Fin h)) (Fin N))
      (firstAccepted E (n := N)))
      ((Finset.univ.filter fun x => (1/(5*q))*h≤hits H x).image some) ≤
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card) := by
  let b : ℝ := 1/(5*q)
  have hb : 0<b := by dsimp [b]; positivity
  have hepos : 0<eventMass (iid (uniformOn A hA) (Fin h)) E := by linarith
  have hp := uniform_proposal_bad A W hA hW hAW h N hN E
    (Finset.univ.filter fun x => b*h≤hits H x) hsource hepos
  have hi := iid_test_rejection (uniformOn A hA) H h hh b hb
  have hs := uniform_source_fraction A X H hA hAX c hc hsize
  have hnum : eventMass (iid (uniformOn A hA) (Fin h))
        (Finset.univ.filter fun x => b*h≤hits H x) ≤
      (((H∩X).card:ℝ)/(c*X.card))/b :=
    hi.trans (div_le_div_of_nonneg_right hs hb.le)
  have hd := div_le_div₀ (by positivity) hnum (by norm_num : (0:ℝ)<9/10) hE
  have hnX : (0:ℝ)<X.card := by exact_mod_cast Finset.card_pos.mpr (hA.mono hAX)
  have heq : ((((H∩X).card:ℝ)/(c*X.card))/b)/(9/10)=
      (50*q/(9*c))*(((H∩X).card:ℝ)/X.card) := by
    dsimp [b]
    field_simp
    ring
  have hfin := hp.trans (hd.trans_eq heq)
  convert hfin using 1

theorem fresh_test_prior_average {Θ : Type*} [Fintype Θ] (p : Law Θ)
    (A X W : Θ → Finset α) (H : Finset α)
    (hA : ∀ θ,(A θ).Nonempty) (hW : ∀ θ,(W θ).Nonempty)
    (hAW : ∀ θ,A θ⊆W θ) (hAX : ∀ θ,A θ⊆X θ)
    (q c : ℝ) (hq : 0<q) (hc : 0<c) (hsize : ∀ θ,c*(X θ).card≤(A θ).card)
    (h N : ℕ) (hh : 0<h) (hN : 0<N) (E : Θ → Finset (Fin h → α))
    (hsource : ∀ θ x,x∈E θ → ∀ i,x i∈A θ)
    (hE : ∀ θ,(9:ℝ)/10≤eventMass (iid (uniformOn (A θ) (hA θ)) (Fin h)) (E θ))
    (ready : Θ → Prop) [DecidablePred ready] :
    (∑ θ,p θ*(if ready θ then
      eventMass (map (iid (iid (uniformOn (W θ) (hW θ)) (Fin h)) (Fin N))
        (firstAccepted (E θ) (n := N)))
        ((Finset.univ.filter fun x => (1/(5*q))*h≤hits H x).image some) else 0)) ≤
    (50*q/(9*c))*(∑ θ,p θ*(((H∩X θ).card:ℝ)/(X θ).card)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro θ _
  have hf := fresh_test_domination (A θ) (X θ) (W θ) H (hA θ) (hW θ)
    (hAW θ) (hAX θ) q c hq hc (hsize θ) h N hh hN (E θ) (hsource θ) (hE θ)
  by_cases hr : ready θ
  · rw [ite_eq_left hr]
    calc
      _ ≤ p θ*((50*q/(9*c))*(((H∩X θ).card:ℝ)/(X θ).card)) :=
        mul_le_mul_of_nonneg_left hf (p.nonneg θ)
      _ = _ := by ring
  · rw [ite_eq_right hr,mul_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (p.nonneg θ) (by positivity))

end SharpRamseyFive.FiniteEntropy

end OAI
