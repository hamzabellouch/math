import OAI.Combinatorics.Ryser.LineCover.DeletionDefinitions
import OAI.Combinatorics.Ryser.Probability.Product
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

def contribution (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) : Finset P := deleted ignore a ∩ test

def rare (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) : Prop := (contribution ignore test a).Nonempty

@[simp] theorem contribution_emptyOutcome (ignore : Finset (Finset P))
    (test : Finset P) : contribution ignore test (emptyOutcome shapes D) = ∅ := by
  simp [contribution]

theorem rare_iff_exists (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) :
    rare ignore test a ↔ ∃ x ∈ test, x ∈ deleted ignore a := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
  · rintro ⟨x, hx, hd⟩
    exact ⟨x, Finset.mem_inter.mpr ⟨hd, hx⟩⟩

theorem contribution_card_le (ignore : Finset (Finset P)) (test : Finset P)
    (a : Outcome shapes D) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H) :
    (contribution ignore test a).card ≤ D * H := by
  let A := a.val.filter (fun L => L.val ∉ ignore)
  change (A.biUnion Subtype.val ∩ test).card ≤ D * H
  rw [Finset.biUnion_inter]
  calc
    _ ≤ ∑ L ∈ A, (L.val ∩ test).card := Finset.card_biUnion_le
    _ ≤ ∑ _L ∈ A, H := Finset.sum_le_sum fun L hL =>
      hshape L.val L.property (Finset.mem_filter.mp hL).2
    _ = A.card * H := by simp
    _ ≤ D * H := Nat.mul_le_mul_right H
      ((Finset.card_filter_le a.val _).trans a.property)

private theorem card_sub_card_le_card_of_sdiff_subset
    {A B K : Finset P} (h : A \ B ⊆ K) :
    (A.card : ℝ) - (B.card : ℝ) ≤ (K.card : ℝ) := by
  have hc : A.card ≤ K.card + B.card :=
    (Finset.card_le_card_sdiff_add_card (s := A) (t := B)).trans
      (Nat.add_le_add_right (Finset.card_le_card h) B.card)
  have hr : (A.card : ℝ) ≤ (K.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hc
  linarith

variable [instFintypeP : Fintype P]

def retainedCount (ignore : Finset (Finset P)) (test : Finset P)
    (ω : Fin n → Outcome shapes D) : ℝ :=
  ((survivors ignore ω ∩ test).card : ℝ)

theorem survivors_update_sdiff_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore (Function.update ω i a) ∩ test) \
        (survivors ignore ω ∩ test) ⊆ contribution ignore test (ω i) := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxnew, hxold⟩
  rcases Finset.mem_inter.mp hxnew with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxi
  apply hxold
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hxi
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem survivors_sdiff_update_subset (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    (survivors ignore ω ∩ test) \
        (survivors ignore (Function.update ω i a) ∩ test) ⊆
      contribution ignore test a := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxold, hxnew⟩
  rcases Finset.mem_inter.mp hxold with ⟨hxs, hxP⟩
  refine Finset.mem_inter.mpr ⟨?_, hxP⟩
  by_contra hxa
  apply hxnew
  refine Finset.mem_inter.mpr ⟨mem_survivors.mpr ?_, hxP⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hxa
  · have hj := mem_survivors.mp hxs j
    simpa only [Function.update_of_ne hji] using hj

theorem retainedCount_update_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    -((contribution ignore test a).card : ℝ) ≤
        retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω ≤
        ((contribution ignore test (ω i)).card : ℝ) := by
  have hup := card_sub_card_le_card_of_sdiff_subset
    (survivors_update_sdiff_subset ignore test ω i a)
  have hdown := card_sub_card_le_card_of_sdiff_subset
    (survivors_sdiff_update_subset ignore test ω i a)
  change -((contribution ignore test a).card : ℝ) ≤
      ((survivors ignore (Function.update ω i a) ∩ test).card : ℝ) -
        ((survivors ignore ω ∩ test).card : ℝ) ∧ _
  exact ⟨by linarith, hup⟩

theorem retainedCount_update_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (a : Outcome shapes D) :
    |retainedCount ignore test (Function.update ω i a) - retainedCount ignore test ω| ≤
      ((contribution ignore test (ω i)).card : ℝ) +
        ((contribution ignore test a).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_update_bounds ignore test ω i a
  have ho : 0 ≤ ((contribution ignore test (ω i)).card : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ((contribution ignore test a).card : ℝ) := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem retainedCount_empty_bounds (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    0 ≤ retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ∧
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) -
        retainedCount ignore test ω ≤ ((contribution ignore test (ω i)).card : ℝ) := by
  simpa only [contribution_emptyOutcome, Finset.card_empty, Nat.cast_zero, neg_zero]
    using retainedCount_update_bounds ignore test ω i (emptyOutcome shapes D)

theorem retainedCount_empty_abs_le (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      ((contribution ignore test (ω i)).card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [abs_sub_comm, abs_of_nonneg hlo]
  exact hhi

theorem not_rare_retainedCount_eq (ignore : Finset (Finset P))
    (test : Finset P) (ω : Fin n → Outcome shapes D) (i : Fin n)
    (h : ¬ rare ignore test (ω i)) :
    retainedCount ignore test ω =
      retainedCount ignore test (Function.update ω i (emptyOutcome shapes D)) := by
  have he : contribution ignore test (ω i) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨hlo, hhi⟩ := retainedCount_empty_bounds ignore test ω i
  rw [he, Finset.card_empty, Nat.cast_zero] at hhi
  linarith

theorem retainedCount_empty_abs_le_mul (ignore : Finset (Finset P))
    (test : Finset P) (H : ℕ)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (ω : Fin n → Outcome shapes D) (i : Fin n) :
    |retainedCount ignore test ω -
        retainedCount ignore test (Function.update ω i (emptyOutcome shapes D))| ≤
      (D : ℝ) * (H : ℝ) := by
  apply (retainedCount_empty_abs_le ignore test ω i).trans
  exact_mod_cast contribution_card_le ignore test (ω i) H hshape

section FiniteExpectations

variable {Ω : Type*} [Fintype Ω]

theorem expectation_card_inter (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.expectation (fun ω => ((S ω ∩ test).card : ℝ)) =
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := let _ := instFintypeP; by
  have hc (ω : Ω) : ((S ω ∩ test).card : ℝ) =
      ∑ x ∈ test, if x ∈ S ω then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp only [FiniteLaw.expectation, hc, Finset.mul_sum,
    FiniteLaw.prob, mul_ite, mul_one, mul_zero]
  calc
    _ = ∑ x ∈ test, ∑ ω, if x ∈ S ω then μ.weight ω else (0 : ℝ) :=
      Finset.sum_comm (s := Finset.univ) (t := test)
        (f := fun (ω : Ω) (x : P) => if x ∈ S ω then μ.weight ω else (0 : ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hx : x ∈ S ω <;> simp only [hx, ite_true, ite_false]

theorem prob_nonempty_inter_le (μ : FiniteLaw Ω) (S : Ω → Finset P)
    (test : Finset P) :
    μ.prob (fun ω => (S ω ∩ test).Nonempty) ≤
      ∑ x ∈ test, μ.prob (fun ω => x ∈ S ω) := by
  rw [← expectation_card_inter μ S test]
  apply μ.prob_le_expectation
  · intro ω
    exact Nat.cast_nonneg _
  · intro ω hω
    exact Nat.one_le_cast.mpr (Finset.one_le_card.mpr hω)

end FiniteExpectations

theorem prob_rare_le (μ : FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    μ.prob (rare ignore test) ≤
      ∑ x ∈ test, μ.prob (fun a => x ∈ deleted ignore a) :=
  prob_nonempty_inter_le μ (deleted ignore) test

theorem expectation_retainedCount (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    (FiniteLaw.pi μ).expectation (retainedCount ignore test) =
      ∑ x ∈ test, (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) :=
  expectation_card_inter (FiniteLaw.pi μ) (survivors ignore) test

theorem prob_mem_survivors (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (x : P) :
    (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ignore ω) =
      ∏ i, (1 - (μ i).prob (fun a => x ∈ deleted ignore a)) := by
  calc
    _ = (FiniteLaw.pi μ).prob (fun ω => ∀ i, x ∉ deleted ignore (ω i)) := by
      congr 1
      funext ω
      exact propext mem_survivors
    _ = ∏ i, (μ i).prob (fun a => x ∉ deleted ignore a) :=
      FiniteLaw.prob_pi μ (fun _ a => x ∉ deleted ignore a)
    _ = _ := by simp_rw [FiniteLaw.prob_compl]

theorem expectation_retainedCount_product
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) :
    (FiniteLaw.pi μ).expectation (retainedCount ignore test) =
      ∑ x ∈ test, ∏ i, (1 - (μ i).prob (fun a => x ∈ deleted ignore a)) := by
  rw [expectation_retainedCount]
  apply Finset.sum_congr rfl
  intro x _
  exact prob_mem_survivors μ ignore x

end RyserCoveringCounterexample.LineCover

end

end OAI
