import OAI.Probability.InvariantIsing.Cavity.CavitySplitSpinTest
import OAI.Probability.InvariantIsing.Cavity.CavityTreeFullRegular
import OAI.Probability.InvariantIsing.Cavity.CavityUniformTreeLimit

namespace OAI

/-! Site symmetry and the vanishing omitted-site error survive averaging
with the actual, system-size dependent cascade tree law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_full_split_tree_spin_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n) :
    Tendsto (fun k =>
      (∫ T, cavityFullTest (μ k) T (eig k) (I k) (u k)
        (cavityFullSpinInsertion Φ (Fin.natAdd (N k) site)) ∂θ k) -
      ∫ T, cavityFullTest (μ k) T (eig k) (I k) (u k)
        (cavitySplitSpinInsertion Φ site) ∂θ k) atTop (𝓝 0) := by
  let O := fun k (T : LabeledTree (depth k)) =>
    cavityFullTest (μ k) T (eig k) (I k) (u k)
      (cavityFullSpinInsertion Φ (Fin.natAdd (N k) site))
  let C := fun k (T : LabeledTree (depth k)) =>
    cavityFullTest (μ k) T (eig k) (I k) (u k) (cavitySplitSpinInsertion Φ site)
  have hlim := cavity_average_zero_of_all_selections θ (fun k T => O k T-C k T)
    (fun T => cavity_full_split_spin_test_tendsto N depth hN hNlim μ T eig I u Φ site)
  apply hlim.congr'
  filter_upwards [] with k
  have hO : Integrable (O k) (θ k) := integrable_of_measurable_abs_le
    (measurable_cavityFullTest_tree _ _ _ _ _) (fun T =>
      cavityFullDisorderTest_abs_le (μ k) T (eig k) (I k) (u k) (fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (N k) site))
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavityFullSpinInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)))
  have hC : Integrable (C k) (θ k) := integrable_of_measurable_abs_le
    (measurable_cavityFullTest_tree _ _ _ _ _) (fun T =>
      cavityFullDisorderTest_abs_le (μ k) T (eig k) (I k) (u k) (fun _ => cavitySplitSpinInsertion (N := N k) Φ site)
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavitySplitSpinInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityTotalSpinOverlap
              ((cavitySpinSplit (N k) n (σ 0).1).1,(cavitySpinSplit (N k) n (σ 1).1).1))))
  exact integral_sub hO hC

lemma cavity_full_tree_site_identity {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (site : Fin N) :
    (∫ T, cavityFullTest μ T eig I u (cavityFullSpinInsertion Φ site) ∂θ) =
      ∫ T, cavityFullTest μ T eig I u
        (fun σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) ∂θ := by
  apply integral_congr_ae
  filter_upwards [] with T
  unfold cavityFullSpinInsertion
  simpa only [mul_assoc] using
    cavity_full_site_identity hN μ T eig I u hu Φ site

end InvariantIsing

end

end OAI
