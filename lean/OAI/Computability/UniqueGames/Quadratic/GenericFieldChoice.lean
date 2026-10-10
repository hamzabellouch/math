import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Quadratic.BlockSpanLemmas
import OAI.Computability.UniqueGames.Quadratic.GenericSubspaceProbability

namespace OAI

section

/-!
# One field for every rank up to a fixed threshold

The extension degree is chosen using only the rank threshold and the requested
genericity error.  In particular it is fixed before the logical dimension in
the later enlargement construction.  A generic top-rank space exists in the
same field.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators
open UniqueGamesTheorem.Gadget.Orientation

noncomputable section

noncomputable instance binaryFieldFintype (d : ℕ) : Fintype (BinaryField d) :=
  Fintype.ofFinite _

/-- Simultaneous quantitative genericity, with the precise threshold order
used by the latent gadget.  The conclusion covers rank zero as well. -/
theorem exists_uniform_generic_field (r₀ : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ r₀ ≤ 3 * d ∧
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction (BinaryField d) r ≤ ε) ∧
      (∃ S : RankSpace (ZMod 2) (Fin 3 → BinaryField d) r₀, IsGeneric S.1) := by
  classical
  have hex (r : ℕ) := exists_generic_subspace_error_numerator (Fin r)
  choose D hD hbound using hex
  let M : ℕ := ∑ r ∈ Finset.range (r₀ + 1), D r
  have hDM (r : ℕ) (hr : r ≤ r₀) : D r ≤ M := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (M : ℚ)) (2 * (M : ℚ) / ε))
  let d := fieldDegree N r₀
  have hd : 0 < d := fieldDegree_pos N r₀
  have hqN : (N : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card] using
        (chosen_binaryField_thresholds N r₀).1)
  have hq : (0 : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast Fintype.card_pos
  have hqM : 2 * (M : ℚ) < Fintype.card (BinaryField d) :=
    (le_max_left _ _).trans_lt (hN.trans hqN)
  have hqε : 2 * (M : ℚ) / ε < Fintype.card (BinaryField d) :=
    (le_max_right _ _).trans_lt (hN.trans hqN)
  have hεq : 2 * (M : ℚ) < (Fintype.card (BinaryField d) : ℚ) * ε :=
    (div_lt_iff₀ hε).mp hqε
  have hsmall (r : ℕ) (hr : r ≤ r₀) :
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ 1 / 2 ∧
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ ε / 2 := by
    have hDr : (D r : ℚ) ≤ M := by exact_mod_cast hDM r hr
    constructor
    · apply (div_le_iff₀ hq).mpr
      nlinarith
    · apply (div_le_iff₀ hq).mpr
      nlinarith
  have hready (r : ℕ) (hr : r ≤ r₀) :=
    hbound r (BinaryField d) (show (D r : ℚ) / Fintype.card (BinaryField d) < 1 by
      have := (hsmall r hr).1
      linarith)
  refine ⟨d, hd, rankThreshold_le_triple_fieldDegree N r₀, ?_, ?_⟩
  · intro r hr
    have hb := (hready r hr).2
    simp only [Fintype.card_fin] at hb
    apply hb.trans
    exact conditional_error_le_of_small _ _
      (div_nonneg (Nat.cast_nonneg _) hq.le) (hsmall r hr).1 (hsmall r hr).2
  · obtain ⟨S, hS⟩ := (hready r₀ le_rfl).1
    refine ⟨⟨S.1, ?_⟩, hS⟩
    simpa only [Fintype.card_fin] using S.2

end

end UniqueGamesTheorem.Quadratic

end

end OAI
