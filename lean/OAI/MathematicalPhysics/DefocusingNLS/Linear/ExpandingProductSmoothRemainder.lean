import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductCommutatorLinear
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothCutoff

namespace OAI

/-! # The product commutator remainder after smooth frequency cutoff -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_expandingProductCommutator_smooth_remainder (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ)) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L R : ℝ) (hL : 1 ≤ L) (hR : 1 ≤ R),
      let q := schwartzTorusSample a (N + 1 : ℕ) L ha1 hN hL K
      ∀ (f : FourierL2) (j : Fin (N + 1) → Fin 12),
      ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j q f -
        expandingProductCommutator a L (N + 1) ha ha1 hN hL j q
          (expandingSmoothLow L R (by linarith) f)‖ ≤ (C / R) * ‖f‖ := by
  obtain ⟨C, hC, hc⟩ := exists_schwartzProductCommutator_high_bound a N ha ha1 hN K
  refine ⟨C, hC, ?_⟩
  intro L R hL hR q f j
  have hp : 0 < R := by linarith
  have hh := hc L R hL hR j (expandingSmoothHigh L R hp f)
    (expandingSmoothHigh_low_zero L R (by linarith) hp f)
  dsimp only at hh
  rw [← torusProductCommutator_physical, LinearIsometryEquiv.norm_map] at hh
  have he : f = expandingSmoothLow L R hp f + expandingSmoothHigh L R hp f := by
    change f = expandingSmoothLow L R hp f + (f - expandingSmoothLow L R hp f)
    abel
  have hmap := congrArg (expandingProductCommutator a L (N + 1) ha ha1 hN hL j q) he
  rw [expandingProductCommutator_add] at hmap
  rw [hmap, add_sub_cancel_left]
  exact hh.trans (mul_le_mul_of_nonneg_left (expandingSmoothHigh_norm_le L R hp f)
    (div_nonneg hC (by linarith)))

end DefocusingNLS

end OAI
