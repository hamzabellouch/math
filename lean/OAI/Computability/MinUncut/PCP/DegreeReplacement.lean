import Mathlib
import OAI.Computability.MinUncut.PCP.GraphTables

namespace OAI

section
open scoped BigOperators

namespace MinUncutGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem replacement_satisfiable [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (h : G.Satisfiable) : (replacementGraph G H).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact ⟨liftLabel G labeling, replacement_complete G H labeling hlabeling⟩

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem replacement_rejectionCount [Fintype E] [Fintype D] [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) :
    (replacementGraph G H).rejectionCount (liftLabel G labeling) =
      G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type,
    replacement_satisfied_inl, replacement_satisfied_inr, Bool.true_eq_false,
    ite_false, Finset.sum_const_zero, Fintype.sum_unique, Nat.zero_add]
  rfl

abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

theorem padded_satisfiable (G : ConstraintGraph V E A) (dummy : V → Type*)
    (h : G.Satisfiable) : (paddedGraph G dummy).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact ⟨labeling, padded_complete G dummy labeling hlabeling⟩

theorem card_paddedDart [Fintype V] [Fintype E] (G : ConstraintGraph V E A)
    (dummy : V → Type*) [∀ v, Fintype (dummy v)] :
    Fintype.card (PaddedDart G dummy) =
      Fintype.card E + ∑ v, Fintype.card (dummy v) := by
  rw [Fintype.card_sum, Fintype.card_sigma]

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type,
    padded_satisfied_inl, padded_satisfied_inr, Bool.true_eq_false,
    ite_false, Finset.sum_const_zero, Nat.add_zero]
  rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

theorem paddedReplacement_rejectionCount
    [Fintype V] [Fintype E] [Fintype D] [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) (labeling : V → A) :
    (paddedReplacementGraph G dummy H).rejectionCount
        (liftLabel (paddedGraph G dummy) labeling) = G.rejectionCount labeling :=
  (replacement_rejectionCount (paddedGraph G dummy) H labeling).trans
    (padded_rejectionCount G dummy labeling)

def noDummyEquiv (G : ConstraintGraph V E A) :
    PaddedDart G (fun _ : V => Empty) ≃ E where
  toFun z := match z with
    | Sum.inl e => e
    | Sum.inr z => Empty.elim z.2
  invFun := Sum.inl
  left_inv := by
    intro z
    cases z with
    | inl e => rfl
    | inr z => exact Empty.elim z.2
  right_inv _ := rfl

end MinUncutGames.Foundations.PCP.DegreeReplacement

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.AssignmentTester

open MinUncutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

theorem truth_nonneg (b : Bool) : 0 ≤ truth b := by cases b <;> norm_num [truth]

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

theorem disagree_xor_le (a b c d : Bool) :
    disagree (a ^^ b) (c ^^ d) ≤ disagree a c + disagree b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [disagree]

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

theorem bitSign_parity (s f : Cube A) : bitSign (parity s f) = walsh s f := by
  have hw : walsh s f = (-1 : ℝ) ^
      (Finset.univ.filter fun a => s a && f a = true).card := by
    simp [walsh, bitSign, Finset.prod_ite]
  rw [hw]
  simpa [parity, bitSign] using
    (sign_power_parity true (Finset.univ.filter fun a => s a && f a = true).card).symm

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign] <;> linarith

theorem parity_xor (s f g : Cube A) :
    parity s (cubeXor f g) = (parity s f ^^ parity s g) := by
  apply bitSign_injective
  rw [bitSign_parity, bitSign_xor, bitSign_parity, bitSign_parity, walsh_xor]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

theorem expect_cubeXor (F : Cube A → ℝ) (g : Cube A) :
    (𝔼 f, F (cubeXor f g)) = 𝔼 f, F f := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_bij (fun f _ => cubeXor f g) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ h _ heq
    have hh := congrArg (fun x => cubeXor x g) heq
    simpa only [cubeXor_right_twice] using hh
  · intro f _
    exact ⟨cubeXor f g, Finset.mem_univ _, cubeXor_right_twice f g⟩
  · intro f _
    rfl

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

theorem distance_nonneg {K : Type*} [Fintype K] (f g : K → Bool) :
    0 ≤ distance f g := by
  apply Finset.expect_nonneg
  intro k _
  exact disagree_nonneg _ _

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

theorem blr_correlation (F : Cube A → Bool) :
    (𝔼 f, 𝔼 g, bitSign (F f) * bitSign (F g) * bitSign (F (cubeXor f g))) =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3 := by
  simp_rw [mul_assoc, ← Finset.mul_expect]
  conv_lhs =>
    enter [2, f, 2, 2, g, 2, 1]
    rw [cubeXor_comm]
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have heq (f : Cube A) : bitSign (F f) *
      (coefficient (fun f => bitSign (F f)) s ^ 2 * walsh s f) =
    coefficient (fun f => bitSign (F f)) s ^ 2 * (bitSign (F f) * walsh s f) := by ring
  simp_rw [heq, ← Finset.mul_expect]
  change coefficient (fun f => bitSign (F f)) s ^ 2 *
    coefficient (fun f => bitSign (F f)) s = _
  ring

theorem blrReject_fourier (F : Cube A → Bool) :
    blrReject F = (1 - ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3) / 2 := by
  unfold blrReject
  simp_rw [disagree_eq, bitSign_xor, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rw [blr_correlation]

theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let c := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, c s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, c t ^ 3) ≤ c s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < c s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        c s ^ 3 ≤ (∑ t, c t ^ 3) * c s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg (c s))
      nlinarith
    have hlt : c s₀ ^ 3 < (∑ t, c t ^ 3) * c s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [c] at hs
  linarith

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

theorem parity_selfCorrect (s x r : Cube A) :
    (parity s r ^^ parity s (cubeXor r x)) = parity s x := by
  rw [parity_xor]
  cases parity s r <;> cases parity s x <;> rfl

theorem selfCorrect_error (F : Cube A → Bool) (s x : Cube A) :
    (𝔼 r, disagree (selfCorrect F x r) (parity s x)) ≤ 2 * distance F (parity s) := by
  have hle (r : Cube A) :
      disagree (selfCorrect F x r) (parity s x) ≤
      disagree (F r) (parity s r) +
        disagree (F (cubeXor r x)) (parity s (cubeXor r x)) := by
    rw [← parity_selfCorrect s x r]
    exact disagree_xor_le _ _ _ _
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hle r)
  rw [Finset.expect_add_distrib,
    expect_cubeXor (fun r => disagree (F r) (parity s r)) x] at h
  change _ ≤ distance F (parity s) + distance F (parity s) at h
  linarith

def singleMask (i : A) : Cube A := fun j => decide (j = i)

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem expect_flipAt (F : Cube A → ℝ) (i : A) :
    (𝔼 f, F (flipAt i f)) = 𝔼 f, F f := by
  simp_rw [flipAt_eq_xor]
  exact expect_cubeXor F _

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

theorem andLawFailure_flipAt_second (s : Cube A) (i : A) (f g : Cube A)
    (hi : s i = true) :
    andLawFailure s f (flipAt i g) =
      (andLawFailure s f g ^^ (parity s f ^^ f i)) := by
  have hAnd : cubeAnd f (flipAt i g) =
      (if f i then flipAt i (cubeAnd f g) else cubeAnd f g) := by
    funext a
    by_cases ha : a = i
    · subst a
      cases hfi : f i <;> simp [cubeAnd, flipAt, hfi]
    · cases f i <;> simp [cubeAnd, flipAt, ha]
  have hg := parity_flipAt s i g hi
  have hfg := parity_flipAt s i (cubeAnd f g) hi
  cases hfi : f i <;> cases hf : parity s f <;>
    cases hg₀ : parity s g <;> cases ha : parity s (cubeAnd f g) <;>
    simp [andLawFailure, hAnd, hg, hfg, hfi, hf, hg₀, ha]

private theorem four_truth_lower (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem parity_and_rejection (s : Cube A) (i j : A)
    (hi : s i = true) (hj : s j = true) (hij : i ≠ j) :
    (1 : ℝ) / 4 ≤ 𝔼 f, 𝔼 g, truth (andLawFailure s f g) := by
  have hpoint (f g : Cube A) : (1 : ℝ) ≤
      truth (andLawFailure s f g) + truth (andLawFailure s f (flipAt i g)) +
      truth (andLawFailure s (flipAt j f) g) +
      truth (andLawFailure s (flipAt j f) (flipAt i g)) := by
    rw [andLawFailure_flipAt_second s i f g hi,
      andLawFailure_flipAt_second s i (flipAt j f) g hi]
    have hD : (parity s (flipAt j f) ^^ (flipAt j f) i) =
        !(parity s f ^^ f i) := by
      rw [parity_flipAt s j f hj]
      simp only [flipAt, ite_eq_right hij]
      cases parity s f <;> cases f i <;> rfl
    rw [hD]
    exact four_truth_lower _ _ _
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hpoint f g))
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  have hinner (f : Cube A) :
      (𝔼 g, truth (andLawFailure s f (flipAt i g))) =
        𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun g => truth (andLawFailure s f g)) i
  have houter : (𝔼 f, 𝔼 g, truth (andLawFailure s (flipAt j f) g)) =
      𝔼 f, 𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun f => 𝔼 g, truth (andLawFailure s f g)) j
  simp only [hinner, houter] at havg
  linarith

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

theorem disagree_triangle (a b c : Bool) :
    disagree a c ≤ disagree a b + disagree b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

theorem andReject_nonneg (F : Cube A → Bool) : 0 ≤ andReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  apply Finset.expect_nonneg
  intro r₀ _
  apply Finset.expect_nonneg
  intro r₁ _
  apply Finset.expect_nonneg
  intro r₂ _
  exact disagree_nonneg _ _

theorem unitReject_nonneg (F : Cube A → Bool) : 0 ≤ unitReject F := by
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

omit [Nonempty K] in
theorem inputReject_nonneg (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) :
    0 ≤ inputReject label σ F := by
  apply Finset.expect_nonneg
  intro k _
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

theorem andReject_transfer (F : Cube A → Bool) (s : Cube A) :
    (𝔼 f, 𝔼 g, truth (andLawFailure s f g)) ≤
      andReject F + 6 * distance F (parity s) := by
  have hlocal (f g : Cube A) : truth (andLawFailure s f g) ≤
      (𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
        disagree (selfCorrect F (cubeAnd f g) r₀)
          (selfCorrect F f r₁ && selfCorrect F g r₂)) +
      6 * distance F (parity s) := by
    have hp (r₀ r₁ r₂ : Cube A) := and_disagree_transfer
      (parity s (cubeAnd f g)) (parity s f) (parity s g)
      (selfCorrect F (cubeAnd f g) r₀) (selfCorrect F f r₁) (selfCorrect F g r₂)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r₀ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun r₁ _ =>
        Finset.expect_le_expect (s := Finset.univ) (fun r₂ _ => hp r₀ r₁ r₂)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
    have h₀ := selfCorrect_error F s (cubeAnd f g)
    have h₁ := selfCorrect_error F s f
    have h₂ := selfCorrect_error F s g
    rw [andLawFailure, truth_xor]
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hlocal f g))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, andReject] using h

theorem parity_zero (f : Cube A) : parity (fun _ => false) f = false := by
  apply bitSign_injective
  rw [bitSign_parity]
  simp [walsh, bitSign]

theorem unitReject_zero_parity (F : Cube A → Bool) :
    1 - 2 * distance F (parity (fun _ => false)) ≤ unitReject F := by
  have herr := selfCorrect_error F (fun _ => false) (fun _ => true)
  simp only [parity_zero] at herr
  have heq : unitReject F +
      (𝔼 r, disagree (selfCorrect F (fun _ => true) r) false) = 1 := by
    unfold unitReject
    rw [← Finset.expect_add_distrib]
    have hp (b : Bool) : disagree b true + disagree b false = 1 := by
      cases b <;> norm_num [disagree]
    simp only [hp, Fintype.expect_const]
  linarith

theorem parity_singleMask_eval (a : A) (f : Cube A) :
    parity (singleMask a) f = f a := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_symm, walsh_singleMask]

theorem inputReject_transfer (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) (a : A) :
    distance σ (label a) ≤ inputReject label σ F +
      2 * distance F (parity (singleMask a)) := by
  have hlocal (k : K) : disagree (σ k) (label a k) ≤
      (𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)) +
        2 * distance F (parity (singleMask a)) := by
    have hp (r : Cube A) := disagree_triangle (σ k)
      (selfCorrect F (fun a => label a k) r) (label a k)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
    simp only [Fintype.expect_const, Finset.expect_add_distrib] at havg
    have herr := selfCorrect_error F (singleMask a) (fun a => label a k)
    simp only [parity_singleMask_eval] at herr
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun k _ => hlocal k)
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, inputReject, distance] using h

theorem tester_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ testerReject label σ F := by
  have hblr := blrReject_nonneg F
  have hand := andReject_nonneg F
  have hunit := unitReject_nonneg F
  have hin := inputReject_nonneg label σ F
  by_cases hb : δ / 64 ≤ blrReject F
  · unfold testerReject
    linarith
  obtain ⟨s, hs⟩ := blr_near_parity F
  by_cases hz : s = fun _ => false
  · subst s
    have hu := unitReject_zero_parity F
    unfold testerReject
    linarith
  have hsome : ∃ i, s i = true := by
    by_contra hh
    push Not at hh
    apply hz
    funext i
    have h := hh i
    cases hi : s i <;> simp_all
  obtain ⟨i, hi⟩ := hsome
  by_cases htwo : ∃ j, i ≠ j ∧ s j = true
  · obtain ⟨j, hij, hj⟩ := htwo
    have ha := parity_and_rejection s i j hi hj hij
    have ht := andReject_transfer F s
    unfold testerReject
    linarith
  · have heq : s = singleMask i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [singleMask, hi]
      · have hj : s j = false := by
          cases hv : s j
          · rfl
          · exact False.elim (htwo ⟨j, Ne.symm hji, hv⟩)
        simp [singleMask, hji, hj]
    subst s
    have ht := inputReject_transfer label σ F i
    have hf := hfar i
    unfold testerReject
    linarith

omit [Fintype A] [DecidableEq A] in
theorem selfCorrect_dictator (a : A) (x r : Cube A) :
    selfCorrect (fun f => f a) x r = x a := by
  change (r a ^^ (r a ^^ x a)) = x a
  cases r a <;> cases x a <;> rfl

omit [Nonempty K] in
theorem tester_perfect_completeness (label : A → K → Bool) (a : A) :
    testerReject label (label a) (fun f => f a) = 0 := by
  have hb : blrReject (fun f : Cube A => f a) = 0 := by
    simp [blrReject, cubeXor, disagree]
  have ha : andReject (fun f : Cube A => f a) = 0 := by
    simp [andReject, selfCorrect_dictator, cubeAnd, disagree]
  have hu : unitReject (fun f : Cube A => f a) = 0 := by
    simp [unitReject, selfCorrect_dictator, disagree]
  have hi : inputReject label (label a) (fun f => f a) = 0 := by
    simp [inputReject, selfCorrect_dictator, disagree]
  simp [testerReject, hb, ha, hu, hi]

def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem event_perfect_completeness (label : A → K → Bool) (a : A)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
      (eventQueries label kind k f g r₀ r₁ r₂ slot)) = true := by
  have hkind : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hreject : eventReject label (label a) (fun x => x a) kind k f g r₀ r₁ r₂ = 0 := by
    rcases hkind with h | h | h | h <;> subst kind
    · simp [eventReject_blr, cubeXor, disagree]
    · simp [eventReject_and, selfCorrect_dictator, cubeAnd, disagree]
    · simp [eventReject_unit, selfCorrect_dictator, disagree]
    · simp [eventReject_input, selfCorrect_dictator, disagree]
  unfold eventReject at hreject
  cases h : eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
    (eventQueries label kind k f g r₀ r₁ r₂ slot)) <;> simp_all [truth]

def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

theorem explicitTesterReject_eq (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) : explicitTesterReject label σ F = testerReject label σ F := by
  unfold explicitTesterReject
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fin.sum_univ_succ, eventReject_blr, eventReject_and, eventReject_unit,
    eventReject_input, testerReject, blrReject, andReject, unitReject, inputReject, add_assoc]

theorem explicit_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ explicitTesterReject label σ F := by
  rw [explicitTesterReject_eq]
  exact tester_proximity_soundness label σ F hδ hδ' hfar

end MinUncutGames.Foundations.PCP.AssignmentTester

end
end

end OAI
