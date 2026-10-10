import OAI.Probability.InvariantIsing.Magnetic.RestrictedSplitSpinTest
import OAI.Probability.InvariantIsing.Cavity.CavityUniformTreeLimit

namespace OAI

/-! Uniform omission error after averaging over the original random tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

theorem restricted_full_split_tree_spin_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ)
    (S : (k : ℕ) → Finset (Spin (N k+n))) (hS : ∀ k, (S k).Nonempty) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n) :
    Tendsto (fun k =>
      (∫ T, restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k)
        (cavityFullSpinInsertion Φ (Fin.natAdd (N k) site)) ∂θ k) -
      ∫ T, restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k)
        (cavitySplitSpinInsertion Φ site) ∂θ k) atTop (𝓝 0) := by
  let O := fun k (T : LabeledTree (depth k)) =>
    restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k)
      (cavityFullSpinInsertion Φ (Fin.natAdd (N k) site))
  let C := fun k (T : LabeledTree (depth k)) =>
    restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k) (cavitySplitSpinInsertion Φ site)
  have hlim := cavity_average_zero_of_all_selections θ (fun k T => O k T-C k T)
    (fun T => restricted_full_split_spin_test_tendsto N depth S hS hN hNlim μ T eig I u Φ site)
  apply hlim.congr'
  filter_upwards [] with k
  have hO : Integrable (O k) (θ k) := integrable_of_measurable_abs_le
    (measurable_restrictedFullTest_tree (S k) (hS k) _ _ _ _ _) (fun T =>
      restrictedCavityFullDisorderTest_abs_le (S k) (hS k) (μ k) T (eig k) (I k) (u k) (fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (N k) site))
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavityFullSpinInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)))
  have hC : Integrable (C k) (θ k) := integrable_of_measurable_abs_le
    (measurable_restrictedFullTest_tree (S k) (hS k) _ _ _ _ _) (fun T =>
      restrictedCavityFullDisorderTest_abs_le (S k) (hS k) (μ k) T (eig k) (I k) (u k) (fun _ => cavitySplitSpinInsertion (N := N k) Φ site)
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavitySplitSpinInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityTotalSpinOverlap
              ((cavitySpinSplit (N k) n (σ 0).1).1,(cavitySpinSplit (N k) n (σ 1).1).1))))
  exact integral_sub hO hC

end InvariantIsing

end

end OAI
