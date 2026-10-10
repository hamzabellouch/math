import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelGrowth
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GromovInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallEscape

namespace OAI

/-! # The cyclic-kernel reduction with its actual generating set

The kernel is finitely generated and admits a symmetric generating set whose
word-ball growth exponent is one smaller than the given ambient exponent.
-/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G]

theorem cyclic_kernel_polynomial_growth_drop
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (C d : ℕ)
    (hvol : ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ (d + 1))
    (q : G →* Multiplicative ℤ) (hq : Function.Surjective q) :
    ∃ T : Finset q.ker, (∀ t ∈ T, t⁻¹ ∈ T) ∧
      Subgroup.closure (T : Set q.ker) = ⊤ ∧
      ∃ K : ℕ, ∀ n, (wordBall T n).card ≤ K * (1 + n) ^ d := by
  have hfg := cyclic_kernel_fg_of_polynomial_growth S hS hgen ⟨C, d + 1, hvol⟩ q hq
  let : Group.FG q.ker := (Group.fg_iff_subgroup_fg q.ker).mpr hfg
  obtain ⟨T, hTinv, hTgen⟩ := exists_symmetric_finite_generating_set (J := q.ker)
  obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
  let A := insert t (T.image q.ker.subtype)
  let m := A.sup (cayleyWordLength S hS hgen)
  have hA (x : G) (hx : x ∈ A) : x ∈ wordBall S m :=
    (cayleyWordLength_le_iff S hS hgen x m).mp (Finset.le_sup hx)
  have htlen : t ∈ wordBall S m := hA t (Finset.mem_insert_self _ _)
  have hTlen (x : q.ker) (hx : x ∈ T) : (x : G) ∈ wordBall S m :=
    hA x (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  exact ⟨T, hTinv, hTgen, C * (1 + 2 * m) ^ (d + 1),
    cyclic_kernel_word_growth_degree_drop q t ht S T m htlen hTlen C d hvol⟩

theorem infinite_wordBall_card_lower [Infinite G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (n : ℕ) : n + 1 ≤ (wordBall S n).card := by
  induction n with
  | zero => simp [wordBall_zero]
  | succ n ih =>
    obtain ⟨y, hy, hy'⟩ := exists_wordBall_escape S hS hgen n
    have hlt : (wordBall S n).card < (wordBall S (n + 1)).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨wordBall_mono S (Nat.le_succ n), ?_⟩
      intro he
      exact hy' (he.symm ▸ hy)
    omega

theorem finite_of_bounded_wordBall_card
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (C : ℕ)
    (hvol : ∀ n, (wordBall S n).card ≤ C) : Finite G := by
  cases finite_or_infinite G with
  | inl h => exact h
  | inr h =>
    let := h
    have hlo := infinite_wordBall_card_lower S hS hgen C
    have hhi := hvol C
    omega

end PolycyclicRecognition

end

end OAI
