import OAI.Probability.InvariantIsing.Cavity.CavityHaarJointUniform
import OAI.Probability.InvariantIsing.Cavity.CavityGroupCovariancePositive
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! Random overlap labels and their fresh Haar marks converge jointly.
The covariance is the actual finite replica Gram matrix, before taking
the weak limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGroupHaarFrame_joint_law_tendsto {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (K : Set L) (hK : IsCompact K)
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (l : (k : ℕ) → X k → L) (hlM : ∀ k, Measurable (l k))
    (hl : ∀ k x, l k x ∈ K)
    (v : (k : ℕ) → X k → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x a i j, |cavityGroupReplicaGram (v k x) a i j| ≤ C)
    (Q : ℕ → ProbabilityMeasure
      (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ))
    (Q₀ : ProbabilityMeasure
      (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ))
    (hQ : ∀ k, (Q k : Measure _) = (P k).map
      (fun x => (l k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (hQ₀ : ∀ᵐ p ∂(Q₀ : Measure (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)), p.2.PosSemidef)
    (F : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, ∫ U,
        F (l k x, cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k) ∂P k) atTop
      (𝓝 (∫ p, ∫ y, F (p.1, y) ∂multivariateGaussian 0 p.2 ∂(Q₀ : Measure (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)))) := by
  classical
  obtain ⟨G, hG⟩ := cavity_gaussian_joint_test_extension F
  let R k x := (l k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))
  have hRM k : Measurable (R k) := by
    let : OpensMeasurableSpace (Fin m → Matrix (Fin r) (Fin r) ℝ) :=
      inferInstanceAs (OpensMeasurableSpace (Fin m → Fin r → Fin r → ℝ))
    refine (hlM k).prodMk ?_
    apply (continuous_cavityGroupReplicaCovariance q).measurable.comp
    unfold cavityGroupReplicaGram
    fun_prop
  have hps k x : (R k x).2.PosSemidef := by
    change (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x))).PosSemidef
    rw [cavityGroupReplicaGram_covariance]
    simpa using Matrix.posSemidef_self_mul_conjTranspose
      (cavityGroupProjectionMatrix (q := q) (v k x))
  have hGI k : (∫ x, G (R k x) ∂P k) = ∫ p, G p ∂(Q k : Measure _) := by
    rw [hQ k, integral_map (hRM k).aemeasurable G.continuous.aestronglyMeasurable]
  have hGlim : Tendsto (fun k => ∫ x, G (R k x) ∂P k) atTop
      (𝓝 (∫ p, G p ∂(Q₀ : Measure (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)))) := by
    simp_rw [hGI]
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim G
  have htarget : (∫ p, G p ∂(Q₀ : Measure (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ))) =
      ∫ p, ∫ y, F (p.1, y) ∂multivariateGaussian 0 p.2 ∂(Q₀ : Measure (L × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)) :=
    integral_congr_ae (hQ₀.mono fun p hp => hG p.1 p.2 hp)
  rw [htarget] at hGlim
  have hdiff := cavityGroupHaarFrame_labeled_average_error_tendsto K hK N hN μ A₀ hA₀
    F C X P l hl v hv
  have hHM k : Measurable (fun x => ∫ U,
      F (l k x, cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k)) := by
    let : OpensMeasurableSpace
        (((a : Fin m) → Fin r → Fin (N k a) → ℝ) ×
          ((a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)) :=
      inferInstanceAs (OpensMeasurableSpace
        (((a : Fin m) → Fin r → Fin (N k a) → ℝ) ×
          ((a : Fin m) → Fin (N k a) → Fin q → ℝ)))
    have hcont : Continuous (fun p :
        ((a : Fin m) → Fin r → Fin (N k a) → ℝ) ×
          ((a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ) =>
        cavityGroupMatrixProjection p.1 p.2) := by
      unfold cavityGroupMatrixProjection
      fun_prop
    have hm := F.continuous.measurable.comp
      (((hlM k).comp measurable_fst).prodMk (hcont.measurable.comp
        (((hvM k).comp measurable_fst).prodMk
          ((measurable_cavityGroupHaarFrames (A₀ k)).comp measurable_snd))))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hHI k : Integrable (fun x => ∫ U,
      F (l k x, cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k)) (P k) := by
    apply integrable_of_measurable_abs_le (hHM k) (c := ‖F‖)
    intro x
    rw [← Real.norm_eq_abs]
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := Measure.pi (μ k)) (C := ‖F‖)
      (ae_of_all _ fun U => F.norm_coe_le_norm _)
  have hGInt k : Integrable (fun x => G (R k x)) (P k) :=
    integrable_of_measurable_abs_le (G.continuous.measurable.comp (hRM k))
      (fun x => by simpa only [← Real.norm_eq_abs] using G.norm_coe_le_norm (R k x))
  have he k : (∫ x, ((∫ U,
      F (l k x, cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
        ∂Measure.pi (μ k)) -
      ∫ y, F (l k x, y) ∂multivariateGaussian 0
        (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)))) ∂P k) =
      (∫ x, ∫ U,
        F (l k x, cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k) ∂P k) - ∫ x, G (R k x) ∂P k := by
    conv_lhs => arg 2; ext x; rw [← hG (l k x) (R k x).2 (hps k x)]
    exact integral_sub (hHI k) (hGInt k)
  simp_rw [he] at hdiff
  convert hdiff.add hGlim using 1 <;> simp

end InvariantIsing

end

end OAI
