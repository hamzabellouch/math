import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.ReverseCap

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma eventMass_filter_mono (p : Law A) (P Q : A→Prop) (h : ∀a,P a → Q a) :
    eventMass p (Finset.univ.filter P) ≤ eventMass p (Finset.univ.filter Q) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,h a (Finset.mem_filter.mp ha).2⟩)
    (fun a _ _=>p.nonneg a)

lemma eventMass_filter_union (p : Law A) (P Q : A→Prop) :
    eventMass p (Finset.univ.filter fun a=>P a∨Q a) ≤
      eventMass p (Finset.univ.filter P)+eventMass p (Finset.univ.filter Q) := by
  simp only [eventMass,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg a]

lemma pair_success_mass (p : Law A) (P Q : A→Prop)
    (hP : eventMass p (Finset.univ.filter fun a=>¬P a) ≤ 1/20)
    (hQ : eventMass p (Finset.univ.filter fun a=>¬Q a) ≤ 1/20) :
    (9:ℝ)/10 ≤ eventMass p (Finset.univ.filter fun a=>P a∧Q a) := by
  have hb : (1:ℝ) ≤ eventMass p (Finset.univ.filter fun a=>P a∧Q a)+
      eventMass p (Finset.univ.filter fun a=>¬P a)+
      eventMass p (Finset.univ.filter fun a=>¬Q a) := by
    calc
      1 = ∑a,p a := p.sum_one.symm
      _ ≤ ∑a,((if P a∧Q a then p a else 0)+(if ¬P a then p a else 0)+
          (if ¬Q a then p a else 0)) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg a]
      _ = _ := by simp only [Finset.sum_add_distrib,eventMass,Finset.sum_filter]
  linarith

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def rejected (R : A→B→Prop) (S : Finset A) {n : ℕ}
    (q : ℝ) (row : Fin n→B) : Finset A :=
  S.filter fun a=>(n:ℝ)/(5*q) ≤ hits (neighbors R a) row

omit [Fintype A] in
lemma expected_rejected_card (R : A→B→Prop) (S : Finset A) (C : Finset B)
    (hC : C.Nonempty) (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 < q) :
    (∑row,iid (uniformOn C hC) (Fin n) row*((rejected R S q row).card:ℝ)) ≤
      (5*q/C.card)*(∑a∈S,((C.filter (R a)).card:ℝ)) := by
  simp only [rejected]
  rw [expected_filter_card,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have he : (1/(5*q))*(n:ℝ)=(n:ℝ)/(5*q) := by ring
  have hh := iid_test_rejection (uniformOn C hC) (neighbors R a) n hn (1/(5*q)) (by positivity)
  rw [he,uniform_neighbor_mass] at hh
  convert hh using 1; first | rfl | (simp only [div_eq_mul_inv,one_mul,inv_inv]; ring)

omit [Fintype A] in
lemma capture_partition (R : A→B→Prop) (S U : Finset A) (hSU : S⊆U)
    {n : ℕ} (q : ℝ) (row : Fin n→B) :
    (S∩cap R U q row).card+(rejected R S q row).card=S.card := by
  have he : S∩cap R U q row=S.filter fun a=>hits (neighbors R a) row < (n:ℝ)/(5*q) := by
    ext a
    simp only [Finset.mem_inter,cap,Finset.mem_filter]
    constructor
    · rintro ⟨ha,_,hw⟩;exact ⟨ha,hw⟩
    · rintro ⟨ha,hw⟩;exact ⟨ha,hSU ha,hw⟩
  rw [he,rejected]
  simpa only [not_lt] using (Finset.card_filter_add_card_filter_not (s := S) (fun a=>hits (neighbors R a) row < (n:ℝ)/(5*q)))

noncomputable def validationRows (R : A→B→Prop) (S U : Finset A) (C : Finset B)
    (n : ℕ) (q M : ℝ) : Finset (Fin n→B) :=
  Finset.univ.filter fun row=>(∀i,row i∈C) ∧ ((cap R U q row).card:ℝ) ≤ M ∧
    (9:ℝ)/10*S.card ≤ (S∩cap R U q row).card

omit [Fintype A] in
theorem validationRows_mass (R : A→B→Prop) (S U : Finset A) (hS : S.Nonempty) (hSU : S⊆U)
    (C : Finset B) (hC : C.Nonempty) (n : ℕ) (hn : 0 < n) (q M : ℝ) (hq : 0 < q) (hM : 0 < M)
    (hmean : ∑row,iid (uniformOn C hC) (Fin n) row*((cap R U q row).card:ℝ) ≤ M/20)
    (hsparse : (5*q/C.card)*(∑a∈S,((C.filter (R a)).card:ℝ)) ≤ (S.card:ℝ)/200) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) (validationRows R S U C n q M) := by
  have he := uniform_row_source C hC (fun row : Fin n→B=>
    ((cap R U q row).card:ℝ) ≤ M ∧ (9:ℝ)/10*S.card ≤ (S∩cap R U q row).card)
  have he' : eventMass (iid (uniformOn C hC) (Fin n)) (validationRows R S U C n q M)=
      eventMass (iid (uniformOn C hC) (Fin n)) (Finset.univ.filter fun row=>
      ((cap R U q row).card:ℝ) ≤ M ∧ (9:ℝ)/10*S.card ≤ (S∩cap R U q row).card) := by
    convert he using 1 <;> congr 1 <;> ext row <;> simp only [validationRows,Finset.mem_filter]
  rw [he']
  apply pair_success_mass
  · have hh := event_markov (iid (uniformOn C hC) (Fin n))
      (fun row=>((cap R U q row).card:ℝ)) (fun _=>Nat.cast_nonneg _) M
      (Finset.univ.filter fun row=>¬((cap R U q row).card:ℝ) ≤ M)
      (fun row hr=>(lt_of_not_ge (Finset.mem_filter.mp hr).2).le)
    apply (mul_le_mul_iff_of_pos_left hM).mp
    exact hh.trans (by simpa [div_eq_mul_inv] using hmean)
  · have hs : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hh := event_markov (iid (uniformOn C hC) (Fin n))
      (fun row=>((rejected R S q row).card:ℝ)) (fun _=>Nat.cast_nonneg _) (S.card/10)
      (Finset.univ.filter fun row=>¬(9:ℝ)/10*S.card ≤ (S∩cap R U q row).card)
      (by
        intro row hr
        have hg := (Finset.mem_filter.mp hr).2
        have hp : ((S∩cap R U q row).card:ℝ)+(rejected R S q row).card=S.card := by
          exact_mod_cast capture_partition R S U hSU q row
        linarith)
    have hb := hh.trans ((expected_rejected_card R S C hC n hn q hq).trans hsparse)
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0:ℝ)<S.card/10)).mp
    nlinarith

end SharpRamseyFive.ReverseCap

end OAI
