import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeExposure
import OAI.Combinatorics.RamseyFive.Entropy.EvictionDrift

namespace OAI

namespace SharpRamseyFive.TreeCodec

section
open FiniteEntropy BinaryTree ReverseCap
open scoped Classical BigOperators
universe u v w z
variable {I : Type u} {A B : Type v} [Fintype A] [Fintype B]
  (Ω : I → (Finset A × Finset B) → Type w) [∀ i c, Fintype (Ω i c)]
  (p : ∀ i c, Law (Ω i c)) (M : ∀ i c, Ω i c → Type z)
  (out : ∀ i c t, M i c t → Finset A × Finset B)

noncomputable def capLeft (i : I) (c : Finset A × Finset B) (t : Ω i c)
    (m : M i c t) : Finset A × Finset B := (c.1 ∩ (out i c t m).1, c.2)
noncomputable def capRight (i : I) (c : Finset A × Finset B) (t : Ω i c)
    (m : M i c t) : Finset A × Finset B := (c.1, c.2 ∩ (out i c t m).2)

theorem first_context_eviction (enc : ∀ i c t, Option (M i c t))
    (X : Finset A) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).1)))) ≤ ρ i)
    (b : BinaryTree I) (c : Finset A × Finset B) (j : Address b) :
    (∑ ω, tapeLaw Ω p b ω *
      (contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω c j).elim 0
        (fun C => evictionFraction X C.1)) ≤
      evictionFraction X c.1 + pathBudget ρ (fun _ => 0) b j := by
  apply context_cost_bound Ω p M (capLeft Ω M out) (capRight Ω M out) enc
    (fun C => evictionFraction X C.1) (fun _ => evictionFraction_nonneg _ _) ρ (fun _ => 0)
    hρ (fun _ => le_rfl)
  · intro i c
    convert optional_inter_drift (p i c) X c.1
      (fun t => (enc i c t).map (fun m => (out i c t m).1)) (ρ i) (hcap i c) using 1
    apply Finset.sum_congr rfl
    intro t ht
    cases enc i c t <;> rfl
  · intro i c
    simpa only [add_zero] using (show
      (∑ t, p i c t * ((enc i c t).map (capRight Ω M out i c t)).elim 0
        (fun C => evictionFraction X C.1)) ≤ evictionFraction X c.1 from by
      convert optional_constant_drift (p i c) (enc i c) (evictionFraction X c.1)
        (evictionFraction_nonneg _ _) using 1
      apply Finset.sum_congr rfl
      intro t ht
      cases enc i c t <;> rfl)

theorem second_context_eviction (enc : ∀ i c t, Option (M i c t))
    (X : Finset B) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).2)))) ≤ ρ i)
    (b : BinaryTree I) (c : Finset A × Finset B) (j : Address b) :
    (∑ ω, tapeLaw Ω p b ω *
      (contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω c j).elim 0
        (fun C => evictionFraction X C.2)) ≤
      evictionFraction X c.2 + pathBudget (fun _ => 0) ρ b j := by
  apply context_cost_bound Ω p M (capLeft Ω M out) (capRight Ω M out) enc
    (fun C => evictionFraction X C.2) (fun _ => evictionFraction_nonneg _ _) (fun _ => 0) ρ
    (fun _ => le_rfl) hρ
  · intro i c
    simpa only [add_zero] using (show
      (∑ t, p i c t * ((enc i c t).map (capLeft Ω M out i c t)).elim 0
        (fun C => evictionFraction X C.2)) ≤ evictionFraction X c.2 from by
      convert optional_constant_drift (p i c) (enc i c) (evictionFraction X c.2)
        (evictionFraction_nonneg _ _) using 1
      apply Finset.sum_congr rfl
      intro t ht
      cases enc i c t <;> rfl)
  · intro i c
    convert optional_inter_drift (p i c) X c.2
      (fun t => (enc i c t).map (fun m => (out i c t m).2)) (ρ i) (hcap i c) using 1
    apply Finset.sum_congr rfl
    intro t ht
    cases enc i c t <;> rfl

theorem first_original_trim (enc : ∀ i c t, Option (M i c t))
    (X : Finset A) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).1)))) ≤ ρ i)
    (b : BinaryTree I) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ C,
      contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.1).card : ℝ) < (9/10:ℝ)*X.card)) ≤
        10 * pathBudget ρ (fun _ => 0) b j := by
  apply reached_trim_mass _ _ Prod.fst X _
  simpa only [evictionFraction_univ, zero_add] using
    first_context_eviction Ω p M out enc X ρ hρ hcap b (Finset.univ,Finset.univ) j

theorem second_original_trim (enc : ∀ i c t, Option (M i c t))
    (X : Finset B) (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hcap : ∀ i c, (∑ t, p i c t * evictionFraction X
      (ambientTest ((enc i c t).map (fun m => (out i c t m).2)))) ≤ ρ i)
    (b : BinaryTree I) (j : Address b) :
    eventMass (tapeLaw Ω p b) (Finset.univ.filter (fun ω => ∃ C,
      contextAt Ω M (capLeft Ω M out) (capRight Ω M out) enc b ω (Finset.univ,Finset.univ) j = some C ∧
      ((X ∩ C.2).card : ℝ) < (9/10:ℝ)*X.card)) ≤
        10 * pathBudget (fun _ => 0) ρ b j := by
  apply reached_trim_mass _ _ Prod.snd X _
  simpa only [evictionFraction_univ, zero_add] using
    second_context_eviction Ω p M out enc X ρ hρ hcap b (Finset.univ,Finset.univ) j

end

open FiniteEntropy BinaryTree
open scoped Classical BigOperators
universe u v w z
variable {I : Type u}

def pathSum : (b : BinaryTree I) → (Address b → ℝ) → Address b → ℝ
  | .nil, _, j => nomatch j
  | .node _ _ _, f, .inl _ => f (.inl ())
  | .node _ l _, f, .inr (.inl j) => f (.inl ()) + pathSum l (fun k => f (.inr (.inl k))) j
  | .node _ _ r, f, .inr (.inr j) => f (.inl ()) + pathSum r (fun k => f (.inr (.inr k))) j

lemma pathSum_zero (b : BinaryTree I) (j : Address b) : pathSum b (fun _ => 0) j = 0 := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · rfl
    · simp only [pathSum, ihl, add_zero]
    · simp only [pathSum, ihr, add_zero]

lemma pathSum_mono (b : BinaryTree I) (f g : Address b → ℝ) (h : ∀ k, f k ≤ g k)
    (j : Address b) : pathSum b f j ≤ pathSum b g j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · exact h _
    · exact add_le_add (h _) (ihl _ _ (fun k => h _) j)
    · exact add_le_add (h _) (ihr _ _ (fun k => h _) j)

lemma pathSum_const_le_height (b : BinaryTree I) (j : Address b) (a : ℝ) (ha : 0 ≤ a) :
    pathSum b (fun _ => a) j ≤ b.height * a := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    have hL : (l.height:ℝ)+1 ≤ (BinaryTree.node i l r).height := by
      simp only [BinaryTree.height, Nat.cast_add, Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1
    have hR : (r.height:ℝ)+1 ≤ (BinaryTree.node i l r).height := by
      simp only [BinaryTree.height, Nat.cast_add, Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_right _ _) 1
    rcases j with j | (j | j)
    · have hz : (0:ℝ) ≤ l.height := Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_right hL ha
      simpa only [pathSum] using (show a ≤ (BinaryTree.node i l r).height*a by nlinarith only [h, hz, ha])
    · have h := mul_le_mul_of_nonneg_right hL ha
      simpa only [pathSum] using (show a+pathSum l (fun _ => a) j ≤ (BinaryTree.node i l r).height*a by linarith only [h, ihl j])
    · have h := mul_le_mul_of_nonneg_right hR ha
      simpa only [pathSum] using (show a+pathSum r (fun _ => a) j ≤ (BinaryTree.node i l r).height*a by linarith only [h, ihr j])

lemma mean_pathSum {W : Type*} [Fintype W] (p : W → ℝ)
    (b : BinaryTree I) (f : W → Address b → ℝ) (j : Address b) :
    (∑ ω, p ω * pathSum b (f ω) j) = pathSum b (fun k => ∑ ω, p ω * f ω k) j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · rfl
    · simp only [pathSum, mul_add, Finset.sum_add_distrib, ihl]
    · simp only [pathSum, mul_add, Finset.sum_add_distrib, ihr]

variable {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))

noncomputable def abortAt (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) : Option Bool :=
  probe Ω M left right enc (fun i c t => some (enc i c t).isNone) b ω c j
noncomputable def successAt (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) : Option Unit :=
  observe Ω M left right enc (fun _ _ _ _ => ()) b ω c j

omit [Fintype C] [∀ index context, Fintype (Ω index context)] in
theorem missing_path_eq (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    (if successAt Ω M left right enc b ω c j = none then (1:ℝ) else 0) =
      pathSum b (fun k => if abortAt Ω M left right enc b ω c k = some true then 1 else 0) j := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · cases he : enc i c (ω.1 c) <;>
        simp [successAt, abortAt, observe, probe, pathSum, he]
    · cases he : enc i c (ω.1 c) with
      | none => simp [successAt, abortAt, observe, probe, pathSum, he, pathSum_zero]
      | some m =>
          convert ihl ω.2.1 (left i c (ω.1 c) m) j using 1 <;>
            simp [successAt, abortAt, observe, probe, pathSum, he]
          all_goals rfl
    · cases he : enc i c (ω.1 c) with
      | none => simp [successAt, abortAt, observe, probe, pathSum, he, pathSum_zero]
      | some m =>
          convert ihr ω.2.2 (right i c (ω.1 c) m) j using 1 <;>
            simp [successAt, abortAt, observe, probe, pathSum, he]
          all_goals rfl

lemma missing_mass_path (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C) (j : Address b) :
    eventMass p (Finset.univ.filter (fun ω => successAt Ω M left right enc b ω c j = none)) =
      pathSum b (fun k => eventMass p (Finset.univ.filter
        (fun ω => abortAt Ω M left right enc b ω c k = some true))) j := by
  have h := mean_pathSum p b
    (fun ω k => if abortAt Ω M left right enc b ω c k = some true then (1:ℝ) else 0) j
  simp_rw [← missing_path_eq Ω M left right enc b _ c j] at h
  simpa only [eventMass, Finset.sum_filter, mul_ite, mul_one, mul_zero] using h

theorem missing_mass_le (b : BinaryTree I) (p : Law (Tape Ω b)) (c : C)
    (ε : Address b → ℝ)
    (hε : ∀ j, eventMass p (Finset.univ.filter
      (fun ω => abortAt Ω M left right enc b ω c j = some true)) ≤ ε j)
    (j : Address b) :
    eventMass p (Finset.univ.filter (fun ω => successAt Ω M left right enc b ω c j = none)) ≤
      pathSum b ε j := by
  rw [missing_mass_path]
  exact pathSum_mono b _ _ hε j

end SharpRamseyFive.TreeCodec

end OAI
