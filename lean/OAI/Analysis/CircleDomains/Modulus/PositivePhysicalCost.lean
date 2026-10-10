import OAI.Analysis.CircleDomains.Modulus.CountablePhysicalCost

namespace OAI

/-! A positive physical density pays for the physical lengths of all
selected collar fragments. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physicalCost_ge_length (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (c : ℝ≥0∞)
    (hpos : ∀ y ∈ G, c ≤ g y) :
    c * physicalDomainLength e y₀ γ.val ≤ ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ := by
  rw [← dyadicPhysicalOccupation_univ e y₀ γ, ← lintegral_const]
  apply lintegral_mono_ae
  have hmem : ∀ᵐ y ∂dyadicPhysicalOccupation e y₀ γ, y ∈ G := by
    rw [ae_iff]
    exact dyadicPhysicalOccupation_compl e hG y₀ γ
  filter_upwards [hmem] with y hy
  exact hpos y hy

theorem sum_physicalLength_finite_of_cost (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : ℕ → FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : c ≠ 0) (hpos : ∀ y ∈ G, c ≤ g y)
    (hcost : (∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (γ n)) < ∞) :
    (∑' n, physicalDomainLength e y₀ (γ n).val) < ∞ := by
  have hbound : c * (∑' n, physicalDomainLength e y₀ (γ n).val) ≤
      ∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (γ n) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n => physicalCost_ge_length e hG y₀ (γ n) g c hpos
  by_contra hn
  have htop : (∑' n, physicalDomainLength e y₀ (γ n).val) = ∞ :=
    top_le_iff.mp (not_lt.mp hn)
  rw [htop, ENNReal.mul_top hc] at hbound
  exact hcost.not_ge hbound

end CircleDomainRigidity

end

end OAI
