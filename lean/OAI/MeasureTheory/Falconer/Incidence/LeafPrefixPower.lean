import OAI.MeasureTheory.Falconer.Incidence.PlanarLeafInjection
import OAI.MeasureTheory.Falconer.Incidence.BlockProfileBallBound

namespace OAI

/-! Original finite ball bounds become the exact exponential prefix bounds
required by the terminal-center incidence theorem. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem leaf_image_prefix_power_bound {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    {P : Finset (Space 2)} (hball : NormalizedFiniteBallBound δ t K P)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {N : ℕ}
    (l : Space 2 → CellPath 2) (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hsmall : δ ≤ 1/(2:ℝ)^N) :
    ∀ k ≤ N, ∀ p : CellPath 2,
      ((prefixFiber (P.image l) k p).card:ℝ) ≤
        (K*2^t)*(2:ℝ)^(-t*(k:ℝ))*((P.image l).card:ℝ) := by
  intro k hk p
  let r := 2/(2:ℝ)^k
  have hr : 0 < r := by dsimp [r]; positivity
  have hdr : δ ≤ r := by
    calc
      _ ≤ 1/(2:ℝ)^N := hsmall
      _ ≤ 1/(2:ℝ)^k := one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hk)
      _ ≤ _ := by
        dsimp [r]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hc : ((prefixFiber (P.image l) k p).card:ℝ) ≤ K*r^t*((P.image l).card:ℝ) := by
    by_cases hr1 : r ≤ 1
    · apply leaf_image_prefix_count_bound hδ (zero_le_one.trans hK) hball Q (by rw [hQ]; norm_num)
        hk hl hleaf hdr hr1
      rw [hQ]
      have hsqrt : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
      dsimp [r]
      calc
        _ ≤ 2*(1/(2:ℝ)^k) := mul_le_mul_of_nonneg_right hsqrt (by positivity)
        _ = _ := by ring
    · have htotal : ((prefixFiber (P.image l) k p).card:ℝ) ≤ ((P.image l).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have hp : 1 ≤ r^t := Real.one_le_rpow (le_of_lt (lt_of_not_ge hr1)) ht
      exact htotal.trans (le_mul_of_one_le_left (Nat.cast_nonneg _)
        (one_le_mul_of_one_le_of_one_le hK hp))
  have hpow : r^t = (2:ℝ)^t*(2:ℝ)^(-t*(k:ℝ)) := by
    dsimp [r]
    rw [show (2:ℝ)/(2:ℝ)^k = 2*(1/(2:ℝ)^k) by ring,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),dyadic_inverse_power_eq]
  rw [hpow] at hc
  convert hc using 1
  ring

end Falconer

end OAI
