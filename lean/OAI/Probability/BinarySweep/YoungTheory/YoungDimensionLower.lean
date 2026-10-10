import Mathlib
import OAI.Probability.BinarySweep.GridBounds.DiagonalDimension

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma two_pow_card_sub_diagonal_le_dimension (L : ℕ)
    (hL : ∀ x : Cell μ, diagonal μ x < L) :
    2^(Fintype.card (Cell μ)-L) ≤ Module.finrank ℂ (SpechtSpace μ) := by
  let f : Cell μ → Fin L := fun x => ⟨diagonal μ x,hL x⟩
  have hf : fiberStabilizer f = diagonalStabilizer μ := by
    ext g
    constructor
    · intro hg x; exact congrArg Fin.val (hg x)
    · intro hg x; exact Fin.ext (hg x)
  have hb := two_pow_card_sub_colors_le_stabilizer f
  rw [Fintype.card_fin, hf, Nat.card_eq_fintype_card] at hb
  exact hb.trans (diagonal_card_le_dimension μ)

theorem log_dimension_lower :
    (Real.log 2 / 2) *
      (Fintype.card (Cell μ) - max (μ.colLen 0) (μ.rowLen 0) : ℕ) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  let N := Fintype.card (Cell μ)
  let W := max (μ.colLen 0) (μ.rowLen 0)
  let L := (N+W)/2
  have hWN : W ≤ N := height_width_le_card μ
  have hLN : L ≤ N := by dsimp only [L]; omega
  have hnat : N-W ≤ 2*(N-L) := by dsimp only [L]; omega
  have hr : ((N-W : ℕ) : ℝ) ≤ 2*((N-L : ℕ) : ℝ) := by exact_mod_cast hnat
  have hb := two_pow_card_sub_diagonal_le_dimension μ L (diagonal_lt_half_card_add_max μ)
  have hbr : (2 : ℝ)^(N-L) ≤ (Module.finrank ℂ (SpechtSpace μ) : ℝ) := by exact_mod_cast hb
  have hlog := Real.log_le_log (show (0 : ℝ) < 2^(N-L) from by positivity) hbr
  rw [Real.log_pow] at hlog
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change (Real.log 2 / 2) * ((N-W : ℕ) : ℝ) ≤ _
  nlinarith

lemma tail_min_eq_card_sub_max :
    min (Fintype.card (Cell μ) - μ.rowLen 0) (Fintype.card (Cell μ) - μ.colLen 0) =
      Fintype.card (Cell μ) - max (μ.colLen 0) (μ.rowLen 0) := by omega

theorem log_dimension_lower_min_tail :
    (Real.log 2 / 2) *
      (min (Fintype.card (Cell μ)-μ.rowLen 0) (Fintype.card (Cell μ)-μ.colLen 0) : ℕ) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  rw [tail_min_eq_card_sub_max]
  exact log_dimension_lower μ

end BinaryCoordinateSweeps.Young

end

end OAI
