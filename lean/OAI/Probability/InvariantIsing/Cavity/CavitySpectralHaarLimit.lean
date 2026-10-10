import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpectralLabels
import OAI.Probability.InvariantIsing.Cavity.CavityMovingGroupMass
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! The fresh-Haar finite-replica limit under the base Gibbs law. The
only limiting datum is its spectral overlap-array law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_haar_test_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k j, 0 < ρs k j) (hρ0 : ∀ j, 0 < ρ j)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, ∫ U,
      F (spectralBlockView (m + 1) r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
      ∂Measure.pi (μ k) ∂P k) atTop
      (𝓝 (∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
        ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
        ∂(Q₀ : Measure (SpectralArray (m + 1))))) := by
  have hQG k : ∀ᵐ x ∂(Q k : Measure (SpectralArray (m + 1))), SpectralGram x := by
    rw [hQ k, ae_map_iff (ha k).aemeasurable (isClosed_spectralGram _).measurableSet]
    exact ae_of_all _ (hGram k)
  have hQG₀ := spectralArray_limit_gram hlim hQG
  have hGaussian := cavity_spectral_moving_mass_test_tendsto ρs ρ hρ hρs hρ0
    Q Q₀ hlim hQG hQG₀ F
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let b := spectralBlockView (m + 1) r
  let g k : SpectralArray (m + 1) →ᵇ ℝ :=
    G.compContinuous ⟨fun x => (b x, cavitySpectralBlockCovariance q (ρs k) (b x)),
      (continuous_spectralBlockView _ _).prodMk
        ((continuous_cavitySpectralBlockCovariance q (ρs k)).comp (continuous_spectralBlockView _ _))⟩
  let H k x := ∫ U, F (b (a k x),
      cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)
  have hHM k : Measurable (H k) :=
    measurable_cavityGroupHaarFrame_spectral_mean (N k) (μ k) (A₀ k) _
      ((continuous_spectralBlockView _ _).measurable.comp (ha k)) (v k) (hvM k) F
  have hHI k : Integrable (H k) (P k) := by
    apply integrable_of_measurable_abs_le (hHM k) (c := ‖F‖)
    intro x
    rw [← Real.norm_eq_abs]
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := Measure.pi (μ k)) (C := ‖F‖) (f := fun U => F (b (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U)))
      (ae_of_all _ fun U => F.norm_coe_le_norm _)
  have hgI k : Integrable (fun x => g k (a k x)) (P k) :=
    integrable_of_measurable_abs_le ((g k).continuous.measurable.comp (ha k))
      (fun x => by simpa only [← Real.norm_eq_abs] using (g k).norm_coe_le_norm (a k x))
  have hgEq k x : g k (a k x) = ∫ y, F (b (a k x), y)
      ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x))) := by
    rw [hcov k x]
    exact hExt _ _ (cavitySpectralBlockCovariance_posSemidef _
      (fun j => (hρs k j).le) _ (hGram k x))
  have hgMap k : (∫ x, g k (a k x) ∂P k) =
      ∫ x, ∫ y, F (b x, y) ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q (ρs k) (b x))
        ∂(Q k : Measure (SpectralArray (m + 1))) := by
    rw [← integral_map (ha k).aemeasurable (g k).continuous.aestronglyMeasurable, ← hQ k]
    exact integral_congr_ae ((hQG k).mono fun x hx => hExt _ _
      (cavitySpectralBlockCovariance_posSemidef _ (fun j => (hρs k j).le) _ hx))
  have herror : Tendsto (fun k => ∫ x, (H k x - g k (a k x)) ∂P k) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu := cavityGroupHaarFrame_spectral_uniform N hN μ A₀ hA₀ F C (ε / 2) (half_pos hε)
    filter_upwards [hu] with k hk
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const (μ := P k) (C := ε / 2)
      (f := fun x => H k x - g k (a k x)) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, hgEq k x]
        exact (hk (v k x) (b (a k x)) (hv k x)).le)
    exact lt_of_le_of_lt (by simpa only [probReal_univ, mul_one] using hb) (half_lt_self hε)
  have he k : (∫ x, (H k x - g k (a k x)) ∂P k) =
      (∫ x, H k x ∂P k) - ∫ x, ∫ y, F (b x, y)
        ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q (ρs k) (b x))
        ∂(Q k : Measure (SpectralArray (m + 1))) := by
    rw [integral_sub (hHI k) (hgI k), hgMap k]
  simp_rw [he] at herror
  convert herror.add hGaussian using 1 <;> simp [H, b]

end InvariantIsing

end

end OAI
