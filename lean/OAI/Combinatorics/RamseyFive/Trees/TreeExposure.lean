import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ChronologicalCapDomination
import OAI.Combinatorics.RamseyFive.Trees.TreeLaw

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A → C → Type w) [∀ a c, Fintype (Ω a c)]
  (M : ∀ a c, Ω a c → Type z)
  (left right : ∀ a c t, M a c t → C)

def Address : BinaryTree A → Type
  | .nil => Empty
  | .node _ l r => Unit ⊕ Address l ⊕ Address r

noncomputable instance addressFintype (b : BinaryTree A) : Fintype (Address b) := by
  induction b with
  | nil => exact inferInstanceAs (Fintype Empty)
  | node a l r ihl ihr =>
    letI := ihl
    letI := ihr
    exact inferInstanceAs (Fintype (Unit ⊕ Address l ⊕ Address r))

def label : (b : BinaryTree A) → Address b → A
  | .nil, j => nomatch j
  | .node a _ _, .inl _ => a
  | .node _ l _, .inr (.inl j) => label l j
  | .node _ _ r, .inr (.inr j) => label r j

variable {D : Type s}

noncomputable def probe (enc : ∀ a c t, Option (M a c t))
    (test : ∀ a c, Ω a c → Option D) :
    (b : BinaryTree A) → Tape Ω b → C → Address b → Option D
  | .nil, _, _, j => nomatch j
  | .node a _ _, ω, c, .inl _ => test a c (ω.1 c)
  | .node a l _, ω, c, .inr (.inl j) =>
      ((enc a c (ω.1 c)).map (left a c (ω.1 c))).elim none
        (fun c' => probe enc test l ω.2.1 c' j)
  | .node a _ r, ω, c, .inr (.inr j) =>
      ((enc a c (ω.1 c)).map (right a c (ω.1 c))).elim none
        (fun c' => probe enc test r ω.2.2 c' j)

theorem probe_event_bound [Fintype D] (p : ∀ a c, Law (Ω a c))
    (enc : ∀ a c t, Option (M a c t)) (test : ∀ a c, Ω a c → Option D)
    (P : Option D → Prop) (hP : ¬ P none) (B : A → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hlocal : ∀ a c, eventMass (map (p a c)
      (fun t => test a c t)) (Finset.univ.filter P) ≤ B a)
    (b : BinaryTree A) (c : C) (j : Address b) :
    eventMass (map (tapeLaw Ω p b) (fun ω => probe Ω M left right enc test b ω c j))
      (Finset.univ.filter P) ≤ B (label b j) := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · change eventMass (map (tapeLaw Ω p (.node a l r))
        (fun ω => test a c (ω.1 c))) _ ≤ B a
      rw [root_output_law Ω p a l r c (fun t => test a c t)]
      exact hlocal a c
    · let next : Ω a c → Option C := fun t => (enc a c t).map (left a c t)
      let f : Option C → Tape Ω l → Option D := fun x ω =>
        x.elim none (fun c' => probe Ω M left right enc test l ω c' j)
      change eventMass (map (tapeLaw Ω p (.node a l r))
        (fun ω => f (next (ω.1 c)) ω.2.1)) _ ≤ _
      rw [left_continuation_law Ω p a l r c next f, eventMass_map_filter]
      apply adaptive_event_second_le
      intro x
      cases x with
      | none =>
        rw [eventMass_map_filter]
        simp only [f, Option.elim_none]
        simp [hP, eventMass, hB]
      | some c' => exact ihl c' j
    · let next : Ω a c → Option C := fun t => (enc a c t).map (right a c t)
      let f : Option C → Tape Ω r → Option D := fun x ω =>
        x.elim none (fun c' => probe Ω M left right enc test r ω c' j)
      change eventMass (map (tapeLaw Ω p (.node a l r))
        (fun ω => f (next (ω.1 c)) ω.2.2)) _ ≤ _
      rw [right_continuation_law Ω p a l r c next f, eventMass_map_filter]
      apply adaptive_event_second_le
      intro x
      cases x with
      | none =>
        rw [eventMass_map_filter]
        simp only [f, Option.elim_none]
        simp [hP, eventMass, hB]
      | some c' => exact ihr c' j

noncomputable def observe (enc : ∀ a c t, Option (M a c t))
    (out : ∀ a c t, M a c t → D) :
    (b : BinaryTree A) → Tape Ω b → C → Address b → Option D :=
  probe Ω M left right enc (fun a c t => (enc a c t).map (out a c t))

theorem observe_event_bound [Fintype D] (p : ∀ a c, Law (Ω a c))
    (enc : ∀ a c t, Option (M a c t)) (out : ∀ a c t, M a c t → D)
    (P : Option D → Prop) (hP : ¬ P none) (B : A → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hlocal : ∀ a c, eventMass (map (p a c)
      (fun t => (enc a c t).map (out a c t))) (Finset.univ.filter P) ≤ B a)
    (b : BinaryTree A) (c : C) (j : Address b) :
    eventMass (map (tapeLaw Ω p b) (fun ω => observe Ω M left right enc out b ω c j))
      (Finset.univ.filter P) ≤ B (label b j) :=
  probe_event_bound Ω M left right p enc _ P hP B hB hlocal b c j

end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma sum_adaptive (p : Law α) (q : α → Law β) (f : α × β → ℝ) :
    (∑ z, adaptiveLaw p q z * f z) = ∑ a, p a * (∑ b, q a b * f (a,b)) := by
  simp only [adaptiveLaw, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A → C → Type w) [∀ a c, Fintype (Ω a c)]
  (p : ∀ a c, Law (Ω a c))

lemma left_continuation_mean {D : Type s} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (next : Ω a c → Option C) (out : Option C → Tape Ω l → D) (f : D → ℝ) :
    (∑ ω, tapeLaw Ω p (.node a l r) ω * f (out (next (ω.1 c)) ω.2.1)) =
      ∑ t, p a c t * (∑ ω, tapeLaw Ω p l ω * f (out (next t) ω)) := by
  have h := congrArg (fun q : Law D => ∑ x, q x * f x)
    (left_continuation_law Ω p a l r c next out)
  simpa only [sum_map, sum_adaptive, Prod.snd] using h

lemma right_continuation_mean {D : Type s} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (next : Ω a c → Option C) (out : Option C → Tape Ω r → D) (f : D → ℝ) :
    (∑ ω, tapeLaw Ω p (.node a l r) ω * f (out (next (ω.1 c)) ω.2.2)) =
      ∑ t, p a c t * (∑ ω, tapeLaw Ω p r ω * f (out (next t) ω)) := by
  have h := congrArg (fun q : Law D => ∑ x, q x * f x)
    (right_continuation_law Ω p a l r c next out)
  simpa only [sum_map, sum_adaptive, Prod.snd] using h

variable (M : ∀ a c, Ω a c → Type z)
  (left right : ∀ a c t, M a c t → C)

noncomputable def contextAt (enc : ∀ a c t, Option (M a c t)) :
    (b : BinaryTree A) → Tape Ω b → C → Address b → Option C :=
  probe Ω M left right enc (fun _ c _ => some c)

def pathBudget (ρL ρR : A → ℝ) : (b : BinaryTree A) → Address b → ℝ
  | .nil, j => nomatch j
  | .node _ _ _, .inl _ => 0
  | .node a l _, .inr (.inl j) => ρL a + pathBudget ρL ρR l j
  | .node a _ r, .inr (.inr j) => ρR a + pathBudget ρL ρR r j

lemma pathBudget_nonneg (ρL ρR : A → ℝ) (hL : ∀ a, 0 ≤ ρL a) (hR : ∀ a, 0 ≤ ρR a)
    (b : BinaryTree A) (j : Address b) : 0 ≤ pathBudget ρL ρR b j := by
  induction b with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · exact le_rfl
    · exact add_nonneg (hL a) (ihl j)
    · exact add_nonneg (hR a) (ihr j)

theorem context_cost_bound (enc : ∀ a c t, Option (M a c t)) (cost : C → ℝ)
    (_hcost : ∀ c, 0 ≤ cost c) (ρL ρR : A → ℝ)
    (hL : ∀ a, 0 ≤ ρL a) (hR : ∀ a, 0 ≤ ρR a)
    (hleft : ∀ a c, (∑ t, p a c t * ((enc a c t).map (left a c t)).elim 0 cost) ≤ cost c + ρL a)
    (hright : ∀ a c, (∑ t, p a c t * ((enc a c t).map (right a c t)).elim 0 cost) ≤ cost c + ρR a)
    (b : BinaryTree A) (c : C) (j : Address b) :
    (∑ ω, tapeLaw Ω p b ω * (contextAt Ω M left right enc b ω c j).elim 0 cost) ≤
      cost c + pathBudget ρL ρR b j := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [contextAt, probe, Option.elim_some, pathBudget, ← Finset.sum_mul,
        (tapeLaw Ω p (.node a l r)).sum_one, one_mul, add_zero, le_refl]
    · let next : Ω a c → Option C := fun t => (enc a c t).map (left a c t)
      let out : Option C → Tape Ω l → Option C := fun x ω =>
        x.elim none (fun c' => contextAt Ω M left right enc l ω c' j)
      change (∑ ω, tapeLaw Ω p (.node a l r) ω *
        (out (next (ω.1 c)) ω.2.1).elim 0 cost) ≤ cost c + (ρL a + pathBudget ρL ρR l j)
      rw [left_continuation_mean Ω p a l r c next out (fun x => x.elim 0 cost)]
      have ht (t : Ω a c) : (∑ ω, tapeLaw Ω p l ω * (out (next t) ω).elim 0 cost) ≤
          (next t).elim 0 cost + pathBudget ρL ρR l j := by
        cases hx : next t with
        | none => simpa [hx, out] using pathBudget_nonneg ρL ρR hL hR l j
        | some c' => simpa [hx, out] using ihl c' j
      calc
        _ ≤ ∑ t, p a c t * ((next t).elim 0 cost + pathBudget ρL ρR l j) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ht t) ((p a c).nonneg t)
        _ = (∑ t, p a c t * (next t).elim 0 cost) + pathBudget ρL ρR l j := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (p a c).sum_one, one_mul]
        _ ≤ _ := by have h := hleft a c; dsimp only [next]; linarith only [h]
    · let next : Ω a c → Option C := fun t => (enc a c t).map (right a c t)
      let out : Option C → Tape Ω r → Option C := fun x ω =>
        x.elim none (fun c' => contextAt Ω M left right enc r ω c' j)
      change (∑ ω, tapeLaw Ω p (.node a l r) ω *
        (out (next (ω.1 c)) ω.2.2).elim 0 cost) ≤ cost c + (ρR a + pathBudget ρL ρR r j)
      rw [right_continuation_mean Ω p a l r c next out (fun x => x.elim 0 cost)]
      have ht (t : Ω a c) : (∑ ω, tapeLaw Ω p r ω * (out (next t) ω).elim 0 cost) ≤
          (next t).elim 0 cost + pathBudget ρL ρR r j := by
        cases hx : next t with
        | none => simpa [hx, out] using pathBudget_nonneg ρL ρR hL hR r j
        | some c' => simpa [hx, out] using ihr c' j
      calc
        _ ≤ ∑ t, p a c t * ((next t).elim 0 cost + pathBudget ρL ρR r j) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ht t) ((p a c).nonneg t)
        _ = (∑ t, p a c t * (next t).elim 0 cost) + pathBudget ρL ρR r j := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (p a c).sum_one, one_mul]
        _ ≤ _ := by have h := hright a c; dsimp only [next]; linarith only [h]

end SharpRamseyFive.TreeCodec

end OAI
