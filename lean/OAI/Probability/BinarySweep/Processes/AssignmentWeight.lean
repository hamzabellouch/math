import Mathlib
import OAI.Probability.BinarySweep.Processes.IndependentHistory

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section AssignmentWeights
attribute [local instance] Classical.propDecidable
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

def assignmentWeight (p : Equiv.Perm X → ℝ) (A B : I ↪ X) : ℝ :=
  ∑ σ, if Assigns A B σ then p σ else 0

omit [Fintype I] in
lemma assignmentWeight_mono (p q : Equiv.Perm X → ℝ)
    (hpq : ∀ σ, p σ ≤ q σ) (A B : I ↪ X) :
    assignmentWeight p A B ≤ assignmentWeight q A B := by
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hpq σ
  · exact le_rfl

omit [Fintype I] in
lemma assignmentWeight_nonneg {p : Equiv.Perm X → ℝ}
    (hp : ∀ σ, 0 ≤ p σ) (A B : I ↪ X) : 0 ≤ assignmentWeight p A B := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact hp σ
  · exact le_rfl

omit [Fintype I] in
lemma assignmentWeight_smul (p : Equiv.Perm X → ℝ) (c : ℝ) (A B : I ↪ X) :
    assignmentWeight (fun σ => c * p σ) A B = c * assignmentWeight p A B := by
  simp only [assignmentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma assignmentWeight_uniform (A B : I ↪ X) :
    assignmentWeight (fun _ => (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) A B =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ :=
  uniform_assignment_probability A B

lemma assignmentWeight_uniform_pos (A B : I ↪ X) :
    0 < assignmentWeight (fun _ => (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) A B := by
  rw [assignmentWeight_uniform]
  apply inv_pos.mpr
  exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A A.injective)

lemma assignmentWeight_comparison {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) :
    (1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ ≤
      assignmentWeight p A B ∧
    assignmentWeight p A B ≤
      2 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  constructor
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono (fun _ => (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) p hl A B
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono p (fun _ => 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) hu A B

lemma assignmentWeight_ratio_le {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) :
    assignmentWeight p A' B' / assignmentWeight p A B ≤
      4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A A.injective)
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A' A'.injective)
  have hden := (assignmentWeight_comparison hl hu A B).1
  have hnum := (assignmentWeight_comparison hl hu A' B').2
  have hdp : 0 < assignmentWeight p A B :=
    lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hi)) hden
  apply (div_le_iff₀ hdp).mpr
  calc
    _ ≤ 2 * (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)⁻¹ := hnum
    _ = (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) *
          ((1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

end AssignmentWeights

attribute [local instance] Classical.propDecidable

abbrev LinePaths {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) :=
  {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}

def lineInput {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : LinePaths H j y ↪ Slot (bits j) where
  toFun k := H.position j.castSucc k.val j
  inj' k l he := by
    apply Subtype.ext
    apply H.disjoint j.castSucc
    funext i
    by_cases hi : i = j
    · subst i; exact he
    · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm

def lineOutput {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : LinePaths H j y ↪ Slot (bits j) where
  toFun k := H.position j.succ k.val j
  inj' k l he := by
    apply Subtype.ext
    apply H.disjoint j.succ
    funext i
    by_cases hi : i = j
    · subst i; exact he
    · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
      exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm

lemma lineHoles_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : lineHoles H j y ≤ 2 ^ bits j := by
  simpa [lineHoles, Slot, Fintype.card_pi] using
    Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective

lemma sum_lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) : ∑ y, lineHoles H j y = h := by
  classical
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i)))
  simpa only [Fintype.card_sigma, Fintype.card_fin, lineHoles] using hh

lemma pathCost_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    0 ≤ pathCost H := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro y _
  exact fallingCost_nonneg (by positivity) (lineHoles_le H j y)

lemma pathCost_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H ≤ (b : ℝ) * h := by
  calc
    pathCost H ≤ ∑ j : Fin b, ∑ y, (lineHoles H j y : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro y _
      exact fallingCost_le (by positivity) (lineHoles_le H j y)
    _ = _ := by simp only [← Nat.cast_sum, sum_lineHoles]; simp

lemma pathEvent_iff_assigns {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : pathEvent H g ↔
      ∀ (j : Fin b) (y : GridOutside bits j), Assigns (lineInput H j y) (lineOutput H j y) (g j y) := by
  constructor
  · intro hg j y k
    change g j y (H.position j.castSucc k.val j) = H.position j.succ k.val j
    have he := congrArg (fun x : GridSlot bits => x j) (hg j k.val)
    simpa only [gridLayer, Equiv.trans_apply, Equiv.piSplitAt_apply,
      Equiv.prodCongrLeft_apply, Equiv.piSplitAt_symm_apply, dite_true, eq_self,
      lineInput, lineOutput, Function.Embedding.coeFn_mk, k.property] using he
  · intro hg j k
    apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
    simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
    apply Prod.ext
    · exact hg j _ ⟨k, rfl⟩
    · funext i
      exact (H.changes_only_stage j k i.val i.property).symm

lemma finiteLaw_le_one {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω]
    (f : Ω → G) (g : G) : finiteLaw f g ≤ 1 := by
  calc
    _ ≤ ∑ x, finiteLaw f x := Finset.single_le_sum (fun x _ => finiteLaw_nonneg f x) (Finset.mem_univ _)
    _ = 1 := finiteLaw_sum f

def linePerturbationRadius (r : ℕ) : ℝ := 1 / (2 * ((2 ^ (2 * r)).factorial : ℝ))

lemma linePerturbationRadius_pos (r : ℕ) : 0 < linePerturbationRadius r := by
  unfold linePerturbationRadius
  positivity

lemma lineLaw_comparison (r d : ℕ) (hd : d ≤ 2 * r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) (g : Equiv.Perm (Slot d)) :
    (1 / 2 : ℝ) * uniformLaw (Equiv.Perm (Slot d)) g ≤ lineLaw d z g ∧
      lineLaw d z g ≤ 2 * uniformLaw (Equiv.Perm (Slot d)) g := by
  have hf1 : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  have hzp : z ≤ 1 / 2 := hzr.trans (by
    unfold linePerturbationRadius
    apply one_div_le_one_div_of_le (by norm_num)
    linarith)
  have hfd : (Fintype.card (Equiv.Perm (Slot d)) : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast (show Fintype.card (Equiv.Perm (Slot d)) ≤ (2 ^ (2 * r)).factorial from by
      simp only [Fintype.card_perm, Slot, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.factorial_le (Nat.pow_le_pow_right (by norm_num) hd))
  have hup : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    positivity
  have hzU : z ≤ uniformLaw (Equiv.Perm (Slot d)) g := hzr.trans (by
    unfold linePerturbationRadius uniformLaw
    rw [one_div]
    apply inv_anti₀ (by exact_mod_cast Fintype.card_pos)
    linarith)
  have hB0 : 0 ≤ binaryLaw d g := finiteLaw_nonneg _ _
  have hB1 : binaryLaw d g ≤ 1 := finiteLaw_le_one _ _
  constructor
  · unfold lineLaw
    nlinarith
  · unfold lineLaw
    nlinarith [mul_le_mul_of_nonneg_left hB1 hz]

end BinaryCoordinateSweeps
end

end OAI
