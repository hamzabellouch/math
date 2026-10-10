import OAI.Probability.InvariantIsing.Cavity.CavitySelectedReplicaTest
import OAI.Probability.InvariantIsing.Cavity.CavityCappedSpinTest

namespace OAI

/-! The capped spin factor in the Haar comparison is exactly the
finite root/forest/residual spin factor after selecting its assigned axes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityCappedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k))
    (F : (Fin r → Spin k) → ℝ) (y : EuclideanSpace ℝ (Fin r × Fin d)) : ℝ :=
  ∫ ε : Fin r → Spin k,
    (∏ i, Real.exp (min (cavityLogFactor K L C
      (WithLp.toLp 2 (fun a => y (i, a))) (ε i)) τ)) * F ε
        ∂Measure.pi (fun _ => π)

lemma measurable_cavityCappedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) : Measurable (cavityCappedFlatSpinValue K L C τ π F) := by
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin r × Fin d) × (Fin r → Spin k) =>
      (∏ i, Real.exp (min (cavityLogFactor K L C
        (WithLp.toLp 2 (fun a => z.1 (i, a))) (z.2 i)) τ)) * F z.2) := by
    apply measurable_from_prod_countable_left
    intro ε
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro i _
      apply Measurable.exp
      apply Measurable.min _ measurable_const
      exact (continuous_cavityLogFactor K L C (ε i)).measurable.comp (by fun_prop)
    · change Measurable (fun _ : EuclideanSpace ℝ (Fin r × Fin d) => F ε)
      exact measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma cavity_capped_selected_eq_flat {m r d k q : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (e : Fin d → Fin m × Fin q) (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (B : SpectralBlock m r) (z : EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F (B, z) =
      cavityCappedFlatSpinValue K L C τ π (fun ε => F (B, ε))
        (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e) z) := rfl

theorem cavity_selected_capped_spin_test {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n) (σ : Fin r → LabeledLeaf n)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
    (∫ z, cavityCappedSpinReplicaValue K L C τ (cavitySelectedGroupProjection e) π F (B, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho B)) =
      ∫ z, cavityCappedFlatSpinValue K L C τ π (fun ε => F (B, ε))
        (cavityReplicaField n T σ z)
        ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))) := by
  intro B
  simp_rw [cavity_capped_selected_eq_flat]
  exact cavity_selected_group_gaussian_test rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop T σ _ (measurable_cavityCappedFlatSpinValue K L C τ π _)

end InvariantIsing

end

end OAI
