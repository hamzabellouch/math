import OAI.Probability.InvariantIsing.Cavity.CavitySelectedRestrictedSpin
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactor

namespace OAI

/-! Exchange of leaf and Gaussian integration for hard-restricted spin factors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_selected_restricted_spin_average {m d n r k qdim : ℕ}
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
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := fun σ => cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
    (∫ z, ∫ σ, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B σ, ε))
        (cavityReplicaField n T σ z) ∂ν
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n))))) =
      ∫ σ, ∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B σ, z)
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
      cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B zσ.2, ε))
        (cavityReplicaField n T zσ.2 zσ.1)) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B σ, ε))).comp
      (measurable_cavityReplicaField n T σ)
  have hi : Integrable (fun zσ => cavityRestrictedFlatSpinValue K L C τ Bcut π
      (fun ε => F (B zσ.2, ε)) (cavityReplicaField n T zσ.2 zσ.1)) (P.prod ν) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ => cavityRestrictedFlatSpinValue_bound K L C τ Bcut π _
        (fun _ => F.norm_coe_le_norm _) _)
  rw [integral_integral_swap hi]
  exact integral_congr_ae (ae_of_all _ fun σ =>
    (cavity_selected_restricted_spin_test rho lam hrho hsum g e he heg p cut hcut hfirst hlast
      q hq hp htop T σ K L C τ hBcut π F).symm)

end InvariantIsing

end

end OAI
