import OAI.Probability.InvariantIsing.Cavity.CavityGroupCovariancePositive

namespace OAI

/-! Passing from finite spectral-group proportions to their positive
limits in the joint Gaussian marking of the overlap array. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavitySpectralBlockCovariance_tendsto {m r q : ℕ}
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρ0 : ∀ a, ρ a ≠ 0)
    (x : ℕ → SpectralBlock (m + 1) r) (x₀ : SpectralBlock (m + 1) r)
    (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k => cavitySpectralBlockCovariance q (ρs k) (x k)) atTop
      (𝓝 (cavitySpectralBlockCovariance q ρ x₀)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simp only [cavitySpectralBlockCovariance, cavityGroupReplicaCovariance, ite_eq_left hij]
    have hentry : Tendsto (fun k => (x k i.2.1 j.2.1 i.1.castSucc : ℝ)) atTop
        (𝓝 (x₀ i.2.1 j.2.1 i.1.castSucc : ℝ)) :=
      (by fun_prop : Continuous (fun y : SpectralBlock (m + 1) r =>
        (y i.2.1 j.2.1 i.1.castSucc : ℝ))).continuousAt.tendsto.comp hx
    exact hentry.div (tendsto_pi_nhds.mp hρ i.1) (hρ0 i.1)
  · simp only [cavitySpectralBlockCovariance, cavityGroupReplicaCovariance, ite_eq_right hij]
    exact tendsto_const_nhds

theorem cavity_spectral_gaussian_mass_uniform {m r q : ℕ}
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k a, 0 < ρs k a) (hρ0 : ∀ a, 0 < ρ a)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ x : SpectralArray (m + 1), SpectralGram x →
      |(∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r x))) -
        ∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))| < ε := by
  classical
  intro ε hε
  by_contra hbad
  have hf : ∃ᶠ k in atTop, ∃ x : SpectralArray (m + 1), SpectralGram x ∧
      ε ≤ |(∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r x))) -
        ∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))| := by
    simpa only [Filter.not_eventually, not_forall, not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hf
  choose x hx he using hφbad
  obtain ⟨x₀, _, ψ, hψ, hlim⟩ :=
    (isCompact_univ : IsCompact (univ : Set (SpectralArray (m + 1)))).tendsto_subseq
      (fun k => mem_univ (x k))
  have hb := (continuous_spectralBlockView (m + 1) r).continuousAt.tendsto.comp hlim
  have hr : Tendsto (fun k => ρs (φ (ψ k))) atTop (𝓝 ρ) :=
    hρ.comp (hφ.comp hψ).tendsto_atTop
  let S₀ := cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x₀)
  have hS := cavitySpectralBlockCovariance_tendsto (q := q) _ ρ hr
    (fun a => ne_of_gt (hρ0 a)) _ _ hb
  have hT := cavitySpectralBlockCovariance_tendsto (q := q) (fun _ => ρ) ρ
    tendsto_const_nhds (fun a => ne_of_gt (hρ0 a)) _ _ hb
  have hs k : (cavitySpectralBlockCovariance q (ρs (φ (ψ k)))
      (spectralBlockView (m + 1) r (x (ψ k)))).PosSemidef :=
    cavitySpectralBlockCovariance_posSemidef _ (fun a => (hρs _ a).le) _ (hx _)
  have ht k : (cavitySpectralBlockCovariance q ρ
      (spectralBlockView (m + 1) r (x (ψ k)))).PosSemidef :=
    cavitySpectralBlockCovariance_posSemidef _ (fun a => (hρ0 a).le) _ (hx _)
  have hs₀ : S₀.PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hT (Eventually.of_forall ht)
  have hleft := cavity_gaussian_joint_test_tendsto _ _ hb _ S₀ hs hs₀ hS F
  have hright := cavity_gaussian_joint_test_tendsto _ _ hb _ S₀ ht hs₀ hT F
  have hz := (hleft.sub hright).abs
  simp only [sub_self, abs_zero] at hz
  obtain ⟨k, hk⟩ := (hz.eventually (Iio_mem_nhds hε)).exists
  exact (not_le_of_gt hk) (he (ψ k))

theorem cavity_spectral_moving_mass_test_tendsto {m r q : ℕ}
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k a, 0 < ρs k a) (hρ0 : ∀ a, 0 < ρ a)
    (P : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (P₀ : ProbabilityMeasure (SpectralArray (m + 1))) (hP : Tendsto P atTop (𝓝 P₀))
    (hG : ∀ k, ∀ᵐ x ∂(P k : Measure (SpectralArray (m + 1))), SpectralGram x)
    (hG₀ : ∀ᵐ x ∂(P₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
      ∂multivariateGaussian 0
        (cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r x))
      ∂(P k : Measure (SpectralArray (m + 1)))) atTop
      (𝓝 (∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
        ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
        ∂(P₀ : Measure (SpectralArray (m + 1))))) := by
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let b := spectralBlockView (m + 1) r
  let f (ρ' : Fin m → ℝ) : SpectralArray (m + 1) →ᵇ ℝ :=
    G.compContinuous ⟨fun x => (b x, cavitySpectralBlockCovariance q ρ' (b x)),
      (continuous_spectralBlockView _ _).prodMk
        ((continuous_cavitySpectralBlockCovariance q ρ').comp (continuous_spectralBlockView _ _))⟩
  have he (ρ' : Fin m → ℝ) (hρ' : ∀ a, 0 ≤ ρ' a) (x : SpectralArray (m + 1))
      (hx : SpectralGram x) :
      f ρ' x = ∫ y, F (b x, y) ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ' (b x)) :=
    hExt _ _ (cavitySpectralBlockCovariance_posSemidef ρ' hρ' x hx)
  have herror : Tendsto (fun k => ∫ x, (f (ρs k) x - f ρ x)
      ∂(P k : Measure (SpectralArray (m + 1)))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu := cavity_spectral_gaussian_mass_uniform ρs ρ hρ hρs hρ0 F (ε / 2) (half_pos hε)
    filter_upwards [hu] with k hk
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const
      (μ := (P k : Measure (SpectralArray (m + 1)))) (f := fun x => f (ρs k) x - f ρ x)
      (C := ε / 2) ((hG k).mono fun x hx => by
        rw [Real.norm_eq_abs, he _ (fun a => (hρs k a).le) x hx,
          he _ (fun a => (hρ0 a).le) x hx]
        exact (hk x hx).le)
    exact lt_of_le_of_lt (by simpa only [probReal_univ, mul_one] using hb) (half_lt_self hε)
  have hi (k : ℕ) (ρ' : Fin m → ℝ) (hρ' : ∀ a, 0 ≤ ρ' a) :
      (∫ x, f ρ' x ∂(P k : Measure (SpectralArray (m + 1)))) =
        ∫ x, ∫ y, F (b x, y)
          ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ' (b x))
          ∂(P k : Measure (SpectralArray (m + 1))) :=
    integral_congr_ae ((hG k).mono fun x hx => he ρ' hρ' x hx)
  have hdiff : Tendsto (fun k =>
      (∫ x, ∫ y, F (b x, y)
        ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q (ρs k) (b x))
        ∂(P k : Measure (SpectralArray (m + 1)))) -
      ∫ x, ∫ y, F (b x, y)
        ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ (b x))
        ∂(P k : Measure (SpectralArray (m + 1)))) atTop (𝓝 0) := by
    convert herror using 1
    funext k
    rw [integral_sub ((f (ρs k)).integrable _) ((f ρ).integrable _),
      hi k (ρs k) (fun a => (hρs k a).le), hi k ρ (fun a => (hρ0 a).le)]
  have hconst := cavity_spectral_frame_gaussian_test_tendsto ρ (fun a => (hρ0 a).le)
    P P₀ hP hG hG₀ F
  convert hdiff.add hconst using 1 <;> simp [b]

end InvariantIsing

end

end OAI
