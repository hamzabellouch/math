import OAI.Analysis.CircleDomains.Probability.LocalizedSquareMass

namespace OAI

/-! A quadratic area bound and a linear occupation lower bound force a
point-hit probability to vanish. This is the local L² estimate. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem local_mass_vanishing {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {g : X → ℝ≥0∞} (hg : Measurable g)
    (hgfin : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hnull : σ (⋂ n, A n) = 0) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (K p : ℝ≥0∞) (hK : K ≠ ∞)
    (harea : ∀ n, σ (A n) ≤ K * (r n : ℝ≥0∞) ^ 2)
    (hmass : ∀ n, (r n : ℝ≥0∞) * p ≤ (σ.withDensity g) (A n)) : p = 0 := by
  have hb (n : ℕ) : p ^ 2 ≤ (∫⁻ x in A n, g x ^ 2 ∂σ) * K := by
    have hmul : p ^ 2 * (r n : ℝ≥0∞) ^ 2 ≤
        ((∫⁻ x in A n, g x ^ 2 ∂σ) * K) * (r n : ℝ≥0∞) ^ 2 := by
      calc
        _ = ((r n : ℝ≥0∞) * p) ^ 2 := by rw [mul_pow, mul_comm]
        _ ≤ ((σ.withDensity g) (A n)) ^ 2 := pow_le_pow_left' (hmass n) 2
        _ ≤ (∫⁻ x in A n, g x ^ 2 ∂σ) * σ (A n) := localized_square_mass_bound σ hg (hA n)
        _ ≤ (∫⁻ x in A n, g x ^ 2 ∂σ) * (K * (r n : ℝ≥0∞) ^ 2) :=
          mul_le_mul' le_rfl (harea n)
        _ = _ := (mul_assoc _ _ _).symm
    exact (ENNReal.mul_le_mul_iff_left
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (hr n).ne'))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)).mp hmul
  have ht := ENNReal.Tendsto.mul_const
    (tendsto_local_square_energy_zero σ hgfin A hA hanti hnull) (Or.inr hK)
  have hp : p ^ 2 ≤ 0 := by
    have ht' : Tendsto (fun n => (∫⁻ x in A n, g x ^ 2 ∂σ) * K) atTop (𝓝 0) := by
      simpa using ht
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht' (Eventually.of_forall hb)
  simpa using (le_antisymm hp bot_le : p ^ 2 = 0)

end CircleDomainRigidity

end

end OAI
