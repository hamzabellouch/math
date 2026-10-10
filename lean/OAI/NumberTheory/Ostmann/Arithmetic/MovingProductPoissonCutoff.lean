import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductFrequency
import OAI.NumberTheory.Ostmann.Characters.CharacterPoissonCutoff

namespace OAI

/-! # The actual product-centered cutoff covers the initial Poisson window -/
namespace Ostmann
open Filter

theorem movingProductNaturalCutoff_zero (T : ℕ → ℝ) (W Y m : ℝ) :
    movingProductNaturalCutoff T W Y m 0 = naturalTransferCutoff (W - Y) m 0 := by
  simp only [movingProductNaturalCutoff, movingProductFrequencyExponent,
    movingProductExponent, naturalTransferCutoff, transferErrorScale,
    pow_zero, one_mul, mul_one, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num)]
  norm_num

theorem eventual_moving_product_poisson_cutoff (H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ m : ℝ in atTop, ∀ (T : ℕ → ℝ) (W Y : ℝ), Y ≤ W →
      H * Real.exp (W - Y) ≤ movingProductNaturalCutoff T W Y m 0 := by
  filter_upwards [eventual_character_poisson_cutoff 0 H hH] with m hm T W Y hYW
  rw [movingProductNaturalCutoff_zero]
  simpa only [add_zero] using hm (W - Y) (sub_nonneg.mpr hYW)

theorem eventual_spectator_product_poisson_cutoff (k : ℕ) (hk : 0 < k)
    (H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (T : ℕ → ℝ) (W Y : ℝ), Y ≤ W →
      H * Real.exp (W - Y) ≤
        movingProductNaturalCutoff T W Y ((spectatorBulkCount k L : ℝ) / 4) 0 := by
  have ht : Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ) / 4) atTop atTop :=
    (spectatorBulkCount_tendsto k hk).atTop_div_const (by norm_num)
  exact ht.eventually (eventual_moving_product_poisson_cutoff H hH)

end Ostmann

end OAI
