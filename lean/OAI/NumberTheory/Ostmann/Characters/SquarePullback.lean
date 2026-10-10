import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace OAI

/-!
# The factor two in square pullbacks

The finite-fiber bound and Cauchy--Schwarz estimate used in the manuscript's
equation `tree-square-pullback`. Multiplicative characters are extended by zero
at zero, as in the manuscript. Evaluations in these lemmas are at units.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

private theorem square_fiber_card_le_two {ι K : Type*} [Field K] [DecidableEq K]
    (s : Finset ι) (f : ι → K) (hf : Function.Injective f) (y : K) :
    (s.filter fun x => f x ^ 2 = y).card ≤ 2 := by
  classical
  let t := s.filter fun x => f x ^ 2 = y
  by_cases ht : t.Nonempty
  · obtain ⟨a, ha⟩ := ht
    have haeq : f a ^ 2 = y := (Finset.mem_filter.mp ha).2
    have hsub : t.image f ⊆ {f a, -f a} := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      have hbeq : f b ^ 2 = y := (Finset.mem_filter.mp hb).2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (sq_eq_sq_iff_eq_or_eq_neg.mp (hbeq.trans haeq.symm))
    calc
      t.card = (t.image f).card := (Finset.card_image_of_injective t hf).symm
      _ ≤ ({f a, -f a} : Finset K).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · have : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change t.card ≤ 2
    simp only [this, Finset.card_empty, Nat.zero_le]

/-- Squaring has at most two preimages among the units of a prime field. -/
theorem unit_square_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (s : Finset (ZMod p)ˣ) (u : (ZMod p)ˣ) :
    (s.filter fun x => x ^ 2 = u).card ≤ 2 := by
  classical
  have heq : (s.filter fun x => x ^ 2 = u) =
      s.filter (fun x : (ZMod p)ˣ => (x : ZMod p) ^ 2 = (u : ZMod p)) := by
    ext x
    simp only [Finset.mem_filter, ← Units.val_pow_eq_pow_val, Units.val_inj]
  rw [heq]
  exact square_fiber_card_le_two s (fun x : (ZMod p)ˣ => (x : ZMod p))
    Units.val_injective (u : ZMod p)

/-- The same two-point bound applies on the character group of a prime field. -/
theorem mulChar_square_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (ρ : MulChar (ZMod p) ℂ) :
    (s.filter fun χ => χ ^ 2 = ρ).card ≤ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hinj : Function.Injective (fun χ : MulChar (ZMod p) ℂ => χ g) := by
    intro χ ψ h
    exact (MulChar.eq_iff hg χ ψ).mpr h
  have hsub : (s.filter fun χ => χ ^ 2 = ρ) ⊆
      s.filter (fun χ => χ g ^ 2 = ρ g) := by
    intro χ hχ
    obtain ⟨hs, hχ⟩ := Finset.mem_filter.mp hχ
    refine Finset.mem_filter.mpr ⟨hs, ?_⟩
    simpa only [MulChar.pow_apply_coe] using congrArg (fun ψ : MulChar (ZMod p) ℂ => ψ g) hχ
  exact (Finset.card_le_card hsub).trans (square_fiber_card_le_two s _ hinj _)

private theorem norm_sq_sum_le_two {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hs : s.card ≤ 2) : ‖∑ x ∈ s, c x‖ ^ 2 ≤ 2 * ∑ x ∈ s, ‖c x‖ ^ 2 := by
  have hn : 0 ≤ ∑ x ∈ s, ‖c x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsum : ‖∑ x ∈ s, c x‖ ≤ ∑ x ∈ s, ‖c x‖ := norm_sum_le _ _
  have hsq : ‖∑ x ∈ s, c x‖ ^ 2 ≤ (∑ x ∈ s, ‖c x‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ x ∈ s, c x)]
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun x => ‖c x‖)
  have hcard : (s.card : ℝ) ≤ 2 := by exact_mod_cast hs
  have hnn : 0 ≤ ∑ x ∈ s, ‖c x‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right hcard hnn))

/-- A multiplicative character has modulus one at each unit. -/
theorem norm_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) : ‖χ u‖ = 1 := by
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

/-- The two surviving Mellin coefficients in a square pullback satisfy the
factor-two estimate, including their unit phases. -/
theorem square_pullback_coefficients {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (c : MulChar (ZMod p) ℂ → ℂ)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), c χ * χ K‖ ^ 2 ≤
      2 * ∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), ‖c χ‖ ^ 2 := by
  have h := norm_sq_sum_le_two (s.filter fun χ => χ ^ 2 = ρ)
    (fun χ => c χ * χ K) (mulChar_square_fiber_card_le_two s ρ)
  simpa only [norm_mul, norm_mulChar_unit, mul_one] using h

end Ostmann

end OAI
