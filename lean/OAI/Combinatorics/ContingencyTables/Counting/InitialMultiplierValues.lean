import OAI.Combinatorics.ContingencyTables.Transport.InitialDefectChoices
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialization

namespace OAI

/-! # Exact source initial multipliers for actual labelled defects -/

namespace ContingencyTables.InitialMultiplierValues

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates InitialTransversals InitializationBrackets

variable {C : Type*} [Fintype C] (b : C → ℕ)

lemma bracket_hole_of_pos (n : ℕ) (hn : 0< n) : bracket n 1 0=1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact bracket_hole k

lemma bracket_full_of_pos (n : ℕ) (hn : 0< n) :
    bracket n 0 1=((n:ℝ)+1)*((n:ℝ)+2)/6 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [bracket_full]
  push_cast
  ring

lemma bracket_both_of_two (n : ℕ) (hn : 2≤ n) : bracket n 1 1=((n:ℝ)+1)/6 := by
  have he : n=(n-2)+2 := by omega
  conv_lhs => rw [he]
  rw [bracket_both]
  have hc : (n:ℝ)=((n-2:ℕ):ℝ)+2 := by exact_mod_cast he
  rw [hc]
  ring

omit [Fintype C] in
lemma same_cell_capacity (p q : Copy b) (hpq : p≠q) (hcell : p.1=q.1) : 2≤ b p.1 := by
  rcases p with ⟨c,p⟩
  rcases q with ⟨c',q⟩
  simp only at hcell
  subst c'
  have hne : p≠q := fun h => hpq (congrArg (Sigma.mk c) h)
  have hp := p.isLt
  have hq := q.isLt
  have hv : p.val≠q.val := fun h => hne (Fin.ext h)
  change 2≤b c
  omega

noncomputable def value (p q : Copy b) : ℝ :=
  if p.1=q.1 then 6 else 6*((b p.1:ℝ)+1)/((b q.1:ℝ)+2)

omit [Fintype C] in
lemma value_positive (p q : Copy b) : 0< value b p q := by
  unfold value
  split_ifs <;> positivity

lemma bracket_product_same (p q : Copy b) (hpq : p≠q) (hcell : p.1=q.1) :
    (∏ c,bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0))=
      (∏ c,((b c:ℝ)+1))/6 := by
  have he (c : C) :
      bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0)=
        ((b c:ℝ)+1)*(if c=p.1 then (1/6:ℝ) else 1) := by
    by_cases hc : p.1=c
    · subst c
      simp only [hcell,ite_true,bracket_both_of_two (b q.1) (by
        simpa only [hcell] using same_cell_capacity b p q hpq hcell)]
      ring
    · have hcq : q.1≠c := by rwa [← hcell]
      simp [hc,hcq,Ne.symm hc,bracket_neither]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp
  ring

lemma bracket_product_different (p q : Copy b) (hcell : p.1≠q.1) :
    (∏ c,bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0))=
      (∏ c,((b c:ℝ)+1))*(((b q.1:ℝ)+2)/(6*((b p.1:ℝ)+1))) := by
  have he (c : C) :
      bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0)=
        ((b c:ℝ)+1)*
          ((if c=p.1 then 1/((b p.1:ℝ)+1) else 1)*
            (if c=q.1 then ((b q.1:ℝ)+2)/6 else 1)) := by
    by_cases hp : p.1=c
    · subst c
      have hq : q.1≠p.1 := Ne.symm hcell
      simp only [ite_true,hq,ite_false,hcell,bracket_hole_of_pos (b p.1) (by have := p.2.isLt; omega),
        mul_one]
      field_simp
    · by_cases hq : q.1=c
      · subst c
        simp only [hp,ite_false,ite_true,Ne.symm hp,
          bracket_full_of_pos (b q.1) (by have := q.2.isLt; omega),one_mul]
        ring
      · simp [hp,hq,Ne.symm hp,Ne.symm hq,bracket_neither]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  field_simp

/-- The exact finite transversal/defect ratio is six in a shared cell,
and otherwise six times (b_hole+1)/(b_full+2). -/
theorem ideal_constant [DecidableEq C] (p q : Copy b) (hpq : p≠q) (M : ℝ) (hM : 0< M) :
    slotTotal pairs (LabelledFactorial.firstLift (group (cell b)) (fun _ => M)
      (InitialTransversals.denominator b)) ∅/
      slotDefect pairs (LabelledFactorial.firstLift (group (cell b)) (fun _ => M)
        (InitialTransversals.denominator b)) ∅ (TwoLiftStates.pair p) (TwoLiftStates.pair q)=value b p q := by
  have hd : (inferInstance : DecidableEq C)=Classical.decEq C := Subsingleton.elim _ _
  cases hd
  rw [slotTotal_constant,InitialDefectChoices.slotDefect_constant b p q hpq]
  have hprod : (∏ c,((b c:ℝ)+1))≠0 := ne_of_gt (Finset.prod_pos (fun _ _ => by positivity))
  by_cases hcell : p.1=q.1
  · rw [bracket_product_same b p q hpq hcell]
    simp only [value,hcell,ite_true]
    field_simp [hM.ne',hprod]
  · rw [bracket_product_different b p q hcell]
    simp only [value,hcell,ite_false]
    field_simp [hM.ne',hprod]

end ContingencyTables.InitialMultiplierValues
namespace ContingencyTables.CompanionInitialMultipliers

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionInitialization LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def multiplier (A : Instance I J)
    (p q : (Labels A×Bool)×(Labels A×Bool)) : ℝ :=
  InitialMultiplierValues.value (fun s : SmallCell A => A.b s.val.1 s.val.2) p.1.1 q.1.1

lemma multiplier_positive (A : Instance I J) (p q : (Labels A×Bool)×(Labels A×Bool)) :
    0< multiplier A p q := InitialMultiplierValues.value_positive _ _ _

lemma freeTotal_positive (A : Instance I J) : 0< freeTotal A := by
  apply Finset.prod_pos
  intro a _
  exact Nat.cast_pos.mpr (Nat.succ_pos _)

/-- The explicit rational initial multiplier equals the ideal for the
literal source count, not just for an abstract constant lift. -/
theorem ideal_at_zero (A : Instance I J) (p q : Labels A) (hpq : p≠q) :
    slotTotal pairs (f A 0) ∅/slotDefect pairs (f A 0) ∅ (TwoLiftStates.pair p) (TwoLiftStates.pair q)=
      multiplier A (TwoLiftStates.pair p) (TwoLiftStates.pair q) := by
  have he : f A 0=firstLift (group (labelCell A)) (fun _ => freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext S
    unfold f firstLift
    rw [h_zero]
  rw [he,denominator_eq]
  convert InitialMultiplierValues.ideal_constant
    (fun s : SmallCell A => A.b s.val.1 s.val.2) p q hpq (freeTotal A) (freeTotal_positive A) using 1
  congr 1

/-- Initialization has exact ideals, hence satisfies every good-
multiplier inequality for the actual chain without a sampling event. -/
theorem initial_good (A : Instance I J) : GoodMultipliers pairs (f A 0) (multiplier A) := by
  refine ⟨multiplier_positive A,?_,?_⟩
  · intro p hp q hq hpq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show p∈Finset.univ.toList.map TwoLiftStates.pair from hp)
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp (show q∈Finset.univ.toList.map TwoLiftStates.pair from hq)
    have hab : a≠b := fun h => hpq (congrArg TwoLiftStates.pair h)
    rw [mul_comm (4:ℝ),← div_div,ideal_at_zero A a b hab]
    have hpos := multiplier_positive A (TwoLiftStates.pair a) (TwoLiftStates.pair b)
    linarith
  · intro p hp q hq hpq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show p∈Finset.univ.toList.map TwoLiftStates.pair from hp)
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp (show q∈Finset.univ.toList.map TwoLiftStates.pair from hq)
    have hab : a≠b := fun h => hpq (congrArg TwoLiftStates.pair h)
    rw [mul_div_assoc,ideal_at_zero A a b hab]
    have hpos := multiplier_positive A (TwoLiftStates.pair a) (TwoLiftStates.pair b)
    linarith

end ContingencyTables.CompanionInitialMultipliers

end OAI
