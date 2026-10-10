import OAI.MeasureTheory.Falconer.Radial.PlatePairLoss
import OAI.MeasureTheory.Falconer.Radial.PlatePowerBudget
import OAI.MeasureTheory.Falconer.Radial.PlateScales
import OAI.MeasureTheory.Falconer.Estimates.FirstExclusionShift

namespace OAI

/-! # Summable power bounds for a genuinely new dyadic pair exclusion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem late_plate_power_loss {d : ℕ} (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (j : ℕ) (S : Finset (Space d × ℝ))
    (G : Set (Space d × Space d)) (hGm : MeasurableSet G)
    {A b M s C : ℝ} (hA : 0 < A) (hb : 0 ≤ b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hwidth : 2*M*(plateScale j)^(1/8:ℝ)+3*(A*(plateScale j)^(1/4:ℝ)) ≤
      plateScale (j/32))
    (hsmall : 10*A*(plateScale j)^(1/8:ℝ) ≤ 1)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hcard : (S.card:ℝ) ≤ A*(plateScale j)^(-b))
    (hG : G ⊆ heavyPlateCellPairs ρ Q j (plateScale j) (2*(plateScale j)^b) \
      heavyPlateCellPairs ρ Q (j/32) (plateScale (j/32)) (2*(plateScale (j/32))^b))
    (hcover : heavyPlateCellPairs ρ Q j (plateScale j) (2*(plateScale j)^b) ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
        {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)}) :
    (μ.prod ν) G ≤
      ENNReal.ofReal ((A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ)))*
        (plateScale j)^((s-((d-2:ℕ):ℝ))/8-2*b)) +
      ENNReal.ofReal ((2*(2:ℝ)^b)*(plateScale j)^(b/32)) := by
  have hsmall' : 10*(A*(plateScale j)^(1/4:ℝ))/(plateScale j)^(1/8:ℝ) ≤ 1 := by
    simpa only [plate_intersection_ratio (plateScale_pos j) A] using hsmall
  apply (late_plate_pair_mass μ ν ρ Q j (j/32) S G hGm hM hC
    (mul_pos hA (Real.rpow_pos_of_pos (plateScale_pos j) _))
    (Real.rpow_pos_of_pos (plateScale_pos j) _)
    (Real.rpow_le_one (plateScale_pos j).le (plateScale_le_one j) (by norm_num))
    hwidth hsmall' hν hμbounded hνbounded hfrost hunit hG hcover).trans
  apply add_le_add (plate_card_power_bound (plateScale_pos j) hA.le hcard)
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (plateScale_div_power j hb) (by norm_num : (0:ℝ) ≤ 2)

end Falconer

end OAI
