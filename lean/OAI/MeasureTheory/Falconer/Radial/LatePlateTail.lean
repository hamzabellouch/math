import OAI.MeasureTheory.Falconer.Radial.LatePlatePowerLoss
import OAI.MeasureTheory.Falconer.Radial.PlateLossSeries
import OAI.MeasureTheory.Falconer.Radial.PlateScaleChoices

namespace OAI

/-! # The tail of all first-time plate exclusions has small product mass -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable def dyadicPlateExclusions {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (b : ℝ) (j : ℕ) : Set (Space d × Space d) :=
  heavyPlateCellPairs ρ Q j (plateScale j) (2*(plateScale j)^b)

theorem measurableSet_dyadicPlateExclusions {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (b : ℝ) (j : ℕ) : MeasurableSet (dyadicPlateExclusions ρ Q b j) :=
  measurableSet_heavyPlateCellPairs ρ Q j _ _

theorem eventually_late_plate_tail {d : ℕ} (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (S : ℕ → Finset (Space d × ℝ)) {A b M s C : ℝ}
    (hA : 1 ≤ A) (hb : 0 < b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hgap : 0 < (s-((d-2:ℕ):ℝ))/8-2*b)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ j, ∀ p ∈ S j, ‖p.1‖ = 1)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ A*(plateScale j)^(-b))
    (hcover : ∀ j, dyadicPlateExclusions ρ Q b j ⊆ ⋃ p ∈ S j,
      {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)}) :
    ∀ᶠ j₀ : ℕ in atTop,
      (∑' n : ℕ, (μ.prod ν)
        (firstExclusion (fun i => dyadicPlateExclusions ρ Q b (j₀+i)) (63*j₀+n))) ≤
        ENNReal.ofReal (1/4:ℝ) := by
  let B := A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ))
  let L := 2*(2:ℝ)^b
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨Ng,hNg⟩ := eventually_atTop.mp (eventually_plate_geometry M A)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp
    (eventually_plate_loss_tail hB hgap (by norm_num : (0:ℝ) < 1/8))
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp
    (eventually_plate_loss_tail hL (by linarith : 0 < b/32) (by norm_num : (0:ℝ) < 1/8))
  filter_upwards [eventually_ge_atTop (max 1 (max Ng (max N₁ N₂)))] with j₀ hj₀
  have hj₀pos : 0 < j₀ := by omega
  have hcost : ∀ n : ℕ, (μ.prod ν)
      (firstExclusion (fun i => dyadicPlateExclusions ρ Q b (j₀+i)) (63*j₀+n)) ≤
      ENNReal.ofReal (B*(plateScale (64*j₀+n))^((s-((d-2:ℕ):ℝ))/8-2*b)) +
      ENNReal.ofReal (L*(plateScale (64*j₀+n))^(b/32)) := by
    intro n
    let j := 64*j₀+n
    have hj : j₀+(63*j₀+n) = j := by dsimp [j]; omega
    have hgj := hNg j (by dsimp [j]; omega)
    have hs := firstExclusion_shift_subset (dyadicPlateExclusions ρ Q b)
      j₀ (63*j₀+n) (j/32) (by dsimp [j]; omega) (by dsimp [j]; omega)
    rw [hj] at hs
    have hh := late_plate_power_loss μ ν ρ Q j (S j)
      (firstExclusion (fun i => dyadicPlateExclusions ρ Q b (j₀+i)) (63*j₀+n))
      (measurableSet_firstExclusion _ (fun i => measurableSet_dyadicPlateExclusions ρ Q b _) _)
      (show 0 < A by linarith only [hA]) hb.le hM hC
      (by simpa only [mul_assoc] using hgj.2) hgj.1 hν hμbounded hνbounded hfrost
      (hunit j) (hcard j) hs (hcover j)
    exact hh
  apply (ENNReal.tsum_le_tsum hcost).trans
  rw [ENNReal.tsum_add]
  apply (add_le_add (hN₁ (64*j₀) (by omega)).le (hN₂ (64*j₀) (by omega)).le).trans_eq
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Falconer

end OAI
