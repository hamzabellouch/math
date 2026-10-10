import OAI.Probability.InvariantIsing.Cavity.CavitySelectedCappedSpin

namespace OAI

/-! Bounded capped spin factors may be averaged in either Gaussian-first
or leaf-first order, so the physical Gaussian block and finite cavity
factor have the same averaged replica numerator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavityCappedFlatSpinValue_bound {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) {M : ℝ} (hF : ∀ ε, ‖F ε‖ ≤ M)
    (y : EuclideanSpace ℝ (Fin r × Fin d)) :
    ‖cavityCappedFlatSpinValue K L C τ π F y‖ ≤ (Real.exp τ)^r * M := by
  have hb (ε : Fin r → Spin k) :
      ‖(∏ i, Real.exp (min (cavityLogFactor K L C
        (WithLp.toLp 2 (fun a => y (i, a))) (ε i)) τ)) * F ε‖ ≤ (Real.exp τ)^r * M := by
    rw [norm_mul]
    apply mul_le_mul _ (hF ε) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have hi := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => π)) (ae_of_all _ hb)
  simpa only [cavityCappedFlatSpinValue, probReal_univ, mul_one] using hi

theorem cavity_selected_capped_spin_average {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n)
    (ν : Measure (Fin r → LabeledLeaf n)) [IsProbabilityMeasure ν]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun σ => cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
    (∫ z, ∫ σ, cavityCappedFlatSpinValue K L C τ π (fun ε => F (B σ, ε))
        (cavityReplicaField n T σ z) ∂ν
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n))))) =
      ∫ σ, ∫ z, cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F (B σ, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho (B σ)) ∂ν := by
  intro B
  let P := ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
    (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
    (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
        (Measure.pi (fun _ : Fin r => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))
  have hm : Measurable (fun zσ :
      ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (Fin r → EuclideanSpace ℝ (Fin d))) × (Fin r → LabeledLeaf n) =>
      cavityCappedFlatSpinValue K L C τ π (fun ε => F (B zσ.2, ε))
        (cavityReplicaField n T zσ.2 zσ.1)) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (measurable_cavityCappedFlatSpinValue K L C τ π (fun ε => F (B σ, ε))).comp
      (measurable_cavityReplicaField n T σ)
  have hi : Integrable (fun zσ => cavityCappedFlatSpinValue K L C τ π
      (fun ε => F (B zσ.2, ε)) (cavityReplicaField n T zσ.2 zσ.1)) (P.prod ν) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ => cavityCappedFlatSpinValue_bound K L C τ π _
        (fun _ => F.norm_coe_le_norm _) _)
  rw [integral_integral_swap hi]
  exact integral_congr_ae (ae_of_all _ fun σ =>
    (cavity_selected_capped_spin_test rho lam hrho hsum g e he heg p cut hcut hfirst hlast
      q hq hp htop T σ K L C τ π F).symm)

end InvariantIsing

end

end OAI
