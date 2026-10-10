import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTest
import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockSpinIdentity
import OAI.Probability.InvariantIsing.Cavity.CavitySplitSpinTest

namespace OAI

/-! Finite coordinate averaging of full constrained spin tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing

lemma restricted_full_spin_average {N n m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n → Fin N) :
    restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
      ((n : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1 (site i)) * spinValue ((σ 1).1 (site i)))) =
      (n : ℝ)⁻¹ * ∑ i, restrictedFullTest S hS μ T eig I u (cavityFullSpinInsertion Φ (site i)) := by
  have he : (fun (_ : SpecialOrthogonal N) (σ : Fin 2 → Spin N × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i,
        spinValue ((σ 0).1 (site i)) * spinValue ((σ 1).1 (site i)))) =
      (fun U σ => (n : ℝ)⁻¹ * ∑ i, (fun _ => cavityFullSpinInsertion Φ (site i)) U σ) := by
    funext U σ
    simp only [cavityFullSpinInsertion, ← Finset.mul_sum]
    ring
  unfold restrictedFullTest
  rw [he, restrictedCavityFullDisorderTest_const_mul]
  congr 1
  apply restrictedCavityFullDisorderTest_sum S hS μ T eig I u
    (fun i _ => cavityFullSpinInsertion Φ (site i))
    (fun i => (measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
  intro i U σ
  simpa only [cavityFullSpinInsertion, abs_mul, abs_spinValue, mul_one, one_mul, Real.norm_eq_abs]
    using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)

lemma restricted_full_tree_spin_average {N n m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n → Fin N) :
    (∫ T, restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
      ((n : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1 (site i)) * spinValue ((σ 1).1 (site i)))) ∂θ) =
      (n : ℝ)⁻¹ * ∑ i, ∫ T, restrictedFullTest S hS μ T eig I u
        (cavityFullSpinInsertion Φ (site i)) ∂θ := by
  simp_rw [restricted_full_spin_average S hS μ _ eig I u Φ site]
  rw [integral_const_mul, integral_finsetSum]
  intro i _
  apply integrable_of_measurable_abs_le
    (measurable_restrictedFullTest_tree S hS μ eig I u _)
  intro T
  change |restrictedCavityFullDisorderTest S hS μ T eig I u
    (fun _ => cavityFullSpinInsertion Φ (site i))| ≤ ‖Φ‖
  apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u
    (fun _ => cavityFullSpinInsertion Φ (site i))
    ((measurable_of_countable (cavityFullSpinInsertion Φ (site i))).comp measurable_snd) (norm_nonneg Φ)
  intro U σ
  simpa only [cavityFullSpinInsertion, abs_mul, abs_spinValue, mul_one, one_mul, Real.norm_eq_abs]
    using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)

end InvariantIsing

end

end OAI
