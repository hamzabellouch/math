import OAI.Probability.InvariantIsing.Cavity.CavityCappedSpinTest

namespace OAI

/-! Product-prior factorization of the capped cavity replica test. This
connects the physical base-spin/cavity-spin replicas to the Haar test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_capped_spin_product {X : Type*} [MeasurableSpace X]
    {m r q d k : ℕ} (ν : Measure X) [IsProbabilityMeasure ν]
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (A : (Fin r → X) → SpectralBlock m r) (hA : Measurable A)
    (Z : (Fin r → X) → EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (hJ : ∀ σ i, J (Z σ) i = Y (σ i))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ ξ : Fin r → X × Spin k,
      (∏ i, Real.exp (min (cavityLogFactor K L C (Y (ξ i).1) (ξ i).2) T)) *
        F (A (fun i => (ξ i).1), fun i => (ξ i).2)
      ∂Measure.pi (fun _ => ν.prod π)) =
    ∫ σ, cavityCappedSpinReplicaValue K L C T J π F (A σ, Z σ)
      ∂Measure.pi (fun _ => ν) := by
  let w := fun p : X × Spin k => Real.exp (min (cavityLogFactor K L C (Y p.1) p.2) T)
  have hw : Measurable w := by
    apply measurable_from_prod_countable_left
    intro ε
    exact (((continuous_cavityLogFactor K L C ε).measurable.comp hY).min measurable_const).exp
  let f := fun p : (Fin r → X) × (Fin r → Spin k) =>
    (∏ i, w (p.1 i, p.2 i)) * F (A p.1, p.2)
  have hf : Measurable f := by
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro i _
      exact hw.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
    · exact F.continuous.measurable.comp ((hA.comp measurable_fst).prodMk measurable_snd)
  have hfb p : |f p| ≤ (Real.exp T)^r * ‖F‖ := by
    dsimp only [f]
    rw [abs_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (abs_nonneg _) (by positivity)
    rw [abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hfi : Integrable f
      ((Measure.pi (fun _ : Fin r => ν)).prod (Measure.pi (fun _ : Fin r => π))) :=
    integrable_of_measurable_abs_le hf hfb
  have hp := measurePreserving_arrowProdEquivProdArrow X (Spin k) (Fin r)
    (fun _ => ν) (fun _ => π)
  calc
    _ = ∫ p, f p ∂((Measure.pi (fun _ : Fin r => ν)).prod
        (Measure.pi (fun _ : Fin r => π))) := hp.hasLaw.integral_comp hf.aestronglyMeasurable
    _ = ∫ σ, ∫ ε, f (σ, ε) ∂Measure.pi (fun _ : Fin r => π)
        ∂Measure.pi (fun _ : Fin r => ν) := integral_prod f hfi
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro σ
      simp only [cavityCappedSpinReplicaValue, hJ]
      rfl

end InvariantIsing

end

end OAI
