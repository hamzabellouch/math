import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.IIDLowerTail

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

noncomputable def neighbors (R : A→B→Prop) (a : A) : Finset B :=
  Finset.univ.filter (R a)

noncomputable def cap (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) : Finset A :=
  U.filter fun a=>hits (neighbors R a) row < (n:ℝ)/(5*q)

lemma expected_filter_card {X : Type*} [Fintype X] (p : Law X)
    (U : Finset A) (F : A→X→Prop) :
    (∑x,p x*((U.filter fun a=>F a x).card:ℝ))=
      ∑a∈U,eventMass p (Finset.univ.filter (F a)) := by
  simp only [←Finset.sum_boole,Finset.mul_sum,eventMass,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma uniform_neighbor_mass (R : A→B→Prop) (C : Finset B) (hC : C.Nonempty) (a : A) :
    eventMass (uniformOn C hC) (neighbors R a)=((C.filter (R a)).card:ℝ)/C.card := by
  rw [uniformOn_mass]
  have he : neighbors R a∩C=C.filter (R a) := by
    ext b
    simp [neighbors,and_comm]
  rw [he]

theorem expected_cap_card (R : A→B→Prop) (U Bad : Finset A)
    (C : Finset B) (hC : C.Nonempty) (n : ℕ) (q : ℝ) (hq : 0 < q)
    (hgood : ∀a∈U,a∉Bad → 1/(2*q) ≤ ((C.filter (R a)).card:ℝ)/C.card) :
    (∑row,iid (uniformOn C hC) (Fin n) row*((cap R U q row).card:ℝ)) ≤
      (Bad.card:ℝ)+(U.card:ℝ)*Real.exp (-(n:ℝ)/(20*q)) := by
  simp only [cap]
  rw [expected_filter_card]
  let z := Real.exp (-(n:ℝ)/(20*q))
  have hz : 0 ≤ z := (Real.exp_pos _).le
  calc
    _ ≤ ∑a∈U,((if a∈Bad then (1:ℝ) else 0)+z) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hb : a∈Bad
      · simp only [hb,ite_true]
        exact (eventMass_le_one _ _).trans (by linarith)
      · simp only [hb,ite_false,zero_add]
        apply iid_cap_tail _ _ n q hq
        rw [uniform_neighbor_mass]
        exact hgood a ha hb
    _ = ((U.filter fun a=>a∈Bad).card:ℝ)+U.card*z := by
      rw [Finset.sum_add_distrib,Finset.sum_boole]
      simp
    _ ≤ _ := by
      have hh : (U.filter fun a=>a∈Bad).card ≤ Bad.card :=
        Finset.card_le_card (by intro a ha;exact (Finset.mem_filter.mp ha).2)
      have hh' : ((U.filter fun a=>a∈Bad).card:ℝ) ≤ Bad.card := by exact_mod_cast hh
      exact add_le_add hh' le_rfl

lemma sum_hits (R : A→B→Prop) (S : Finset A) {n : ℕ} (row : Fin n→B) :
    (∑a∈S,hits (neighbors R a) row)=∑i,((S.filter fun a=>R a (row i)).card:ℝ) := by
  simp only [hits,neighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_boole _ _

theorem deterministic_capture (R : A→B→Prop) (S U : Finset A) (hSU : S⊆U)
    (C : Finset B) {n : ℕ} (hn : 0 < n) (q κ : ℝ) (hq : 0 < q)
    (hC : ∀b∈C,((S.filter fun a=>R a b).card:ℝ) ≤ κ*S.card)
    (row : Fin n→B) (hrow : ∀i,row i∈C) :
    (1-5*q*κ)*(S.card:ℝ) ≤ (S∩cap R U q row).card := by
  let t := (n:ℝ)/(5*q)
  let W := S.filter fun a=>hits (neighbors R a) row < t
  let D := S.filter fun a=>¬hits (neighbors R a) row < t
  have ht : 0 < t := by dsimp [t];positivity
  have hpartition : W.card+D.card=S.card := Finset.card_filter_add_card_filter_not _
  have hsum : (∑a∈S,hits (neighbors R a) row) ≤ (n:ℝ)*κ*S.card := by
    rw [sum_hits]
    calc
      _ ≤ ∑i:Fin n,κ*S.card := Finset.sum_le_sum fun i _=>hC _ (hrow i)
      _ = _ := by simp; ring
  have hD : t*(D.card:ℝ) ≤ (n:ℝ)*κ*S.card := by
    calc
      _ = ∑a∈D,t := by simp [mul_comm]
      _ ≤ ∑a∈D,hits (neighbors R a) row :=
        Finset.sum_le_sum fun a ha=>le_of_not_gt (Finset.mem_filter.mp ha).2
      _ ≤ ∑a∈S,hits (neighbors R a) row :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _=>Finset.sum_nonneg fun i _=>by split_ifs <;> norm_num)
      _ ≤ _ := hsum
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hd : (D.card:ℝ) ≤ 5*q*κ*S.card := by
    apply (mul_le_mul_iff_of_pos_left ht).mp
    calc
      _ ≤ (n:ℝ)*κ*S.card := hD
      _ = t*(5*q*κ*S.card) := by dsimp [t];field_simp
  have hpart : (W.card:ℝ)+(D.card:ℝ)=S.card := by exact_mod_cast hpartition
  have he : S∩cap R U q row=W := by
    ext a
    simp only [Finset.mem_inter,cap,Finset.mem_filter,W]
    constructor
    · rintro ⟨ha,_,hw⟩;exact ⟨ha,hw⟩
    · rintro ⟨ha,hw⟩;exact ⟨ha,hSU ha,hw⟩
  rw [he]
  nlinarith

end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma eventMass_filter_partition (p : Law A) (P : A→Prop) :
    eventMass p (Finset.univ.filter P)+
      eventMass p (Finset.univ.filter fun a=>¬P a)=1 := by
  simp only [eventMass,Finset.sum_filter,←Finset.sum_add_distrib]
  convert p.sum_one using 1
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma uniform_row_source (C : Finset A) (hC : C.Nonempty) {n : ℕ}
    (P : (Fin n→A)→Prop) :
    eventMass (iid (uniformOn C hC) (Fin n))
      (Finset.univ.filter fun row=>(∀i,row i∈C)∧P row)=
    eventMass (iid (uniformOn C hC) (Fin n)) (Finset.univ.filter P) := by
  simp only [eventMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hs : ∀i,row i∈C
  · simp [hs]
  · rw [iid_uniformOn]
    simp [hs]

lemma markov_success (p : Law A) (w : A→ℝ) (hw : ∀a,0 ≤ w a)
    (M : ℝ) (hM : 0 < M) (hmean : ∑a,p a*w a ≤ M/10) :
    (9:ℝ)/10 ≤ eventMass p (Finset.univ.filter fun a=>w a ≤ M) := by
  have hbad := event_markov p w hw M (Finset.univ.filter fun a=>¬w a ≤ M)
    (fun a ha=>(lt_of_not_ge (Finset.mem_filter.mp ha).2).le)
  have hp := eventMass_filter_partition p (fun a=>w a ≤ M)
  have hh : eventMass p (Finset.univ.filter fun a=>¬w a ≤ M) ≤ 1/10 := by
    apply (mul_le_mul_iff_of_pos_left hM).mp
    exact hbad.trans (by simpa [div_eq_mul_inv] using hmean)
  linarith

omit [Fintype A] in
lemma firstAccepted_mem {n : ℕ} (E : Finset A) (t : Fin n→A) {a : A}
    (ha : firstAccepted E t=some a) : a∈E := by
  induction n with
  | zero => simp [firstAccepted] at ha
  | succ n ih =>
    rw [firstAccepted] at ha
    split_ifs at ha with h
    · cases Option.some.inj ha
      exact h
    · exact ih _ ha

lemma finite_table_failure (p : Law A) (E : Finset A) (N : ℕ) :
    map (iid p (Fin N)) (firstAccepted E (n := N)) none ≤
      Real.exp (-eventMass p E*N) := by
  rw [first_law_none]
  have hh : 1-eventMass p E ≤ Real.exp (-eventMass p E) := by
    linarith [Real.add_one_le_exp (-eventMass p E)]
  calc
    _ ≤ (Real.exp (-eventMass p E))^N :=
      pow_le_pow_left₀ (sub_nonneg.mpr (eventMass_le_one p E)) hh N
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1;ring

theorem uniform_table_failure (C W : Finset A) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCW : C⊆W) (n N : ℕ) (E : Finset (Fin n→A))
    (hsource : ∀row∈E,∀i,row i∈C)
    (hE : (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) E)
    (q : ℝ) (hN : q ≤ (9:ℝ)/10*((C.card:ℝ)/W.card)^n*N) :
    map (iid (iid (uniformOn W hW) (Fin n)) (Fin N))
      (firstAccepted E (n := N)) none ≤ Real.exp (-q) := by
  have he := eventMass_scaling (iid (uniformOn W hW) (Fin n))
    (iid (uniformOn C hC) (Fin n)) E (((C.card:ℝ)/W.card)^n)
    (fun row hr=>uniformOn_row_scaling C W hC hW hCW row (hsource row hr))
  have hm : (9:ℝ)/10*((C.card:ℝ)/W.card)^n ≤
      eventMass (iid (uniformOn W hW) (Fin n)) E := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hE
      (by positivity : (0:ℝ) ≤ ((C.card:ℝ)/W.card)^n)
    simpa [mul_comm] using hh
  apply (finite_table_failure _ E N).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg N)
  linarith

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

noncomputable def successfulRows (R : A→B→Prop) (U : Finset A)
    (C : Finset B) (n : ℕ) (q M : ℝ) : Finset (Fin n→B) :=
  Finset.univ.filter fun row=>(∀i,row i∈C) ∧ ((cap R U q row).card:ℝ) ≤ M

lemma successfulRows_mass (R : A→B→Prop) (U : Finset A) (C : Finset B)
    (hC : C.Nonempty) (n : ℕ) (q M : ℝ) (hM : 0 < M)
    (hmean : ∑row,iid (uniformOn C hC) (Fin n) row*((cap R U q row).card:ℝ) ≤ M/10) :
    (9:ℝ)/10 ≤ eventMass (iid (uniformOn C hC) (Fin n)) (successfulRows R U C n q M) := by
  rw [successfulRows,uniform_row_source]
  exact markov_success _ _ (fun _=>Nat.cast_nonneg _) M hM hmean

end SharpRamseyFive.ReverseCap

end OAI
