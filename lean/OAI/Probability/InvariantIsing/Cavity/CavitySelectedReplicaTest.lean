import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGroupSelection
import OAI.Probability.InvariantIsing.Cavity.CavityReplicaGaussianAverage

namespace OAI

/-! Measurable tests of the physical selected axes can be evaluated
under the original finite Gaussian root/forest/residual law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavitySelectedGroupProjection {m d r k : ℕ} (e : Fin d → Fin m × Fin k) :
    EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)) :=
  ContinuousLinearMap.pi (fun i =>
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.pi (fun a => EuclideanSpace.proj (cavitySelectedGroupIndex e (i, a)))))

@[simp] lemma cavitySelectedGroupProjection_apply {m d r k : ℕ}
    (e : Fin d → Fin m × Fin k)
    (z : EuclideanSpace ℝ (Fin m × (Fin r × Fin k))) (i : Fin r) (a : Fin d) :
    cavitySelectedGroupProjection e z i a = z (cavitySelectedGroupIndex e (i, a)) := rfl

theorem cavity_selected_group_gaussian_test {m d n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin k)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n) (σ : Fin r → LabeledLeaf n)
    (F : EuclideanSpace ℝ (Fin r × Fin d) → ℝ) (hF : Measurable F) :
    (∫ z, F (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e) z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance k rho
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))) =
      ∫ z, F (cavityReplicaField n T σ z)
        ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
              (Measure.pi (fun _ : Fin r => multivariateGaussian
                (0 : EuclideanSpace ℝ (Fin d))
                (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))) := by
  have hselect := cavity_selected_group_gaussian_law rho lam hrho hsum g e he heg
    p q hq.monotone σ
  have hfield := cavity_finite_replica_field_law rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop T σ
  calc
    _ = ∫ y, F y ∂multivariateGaussian 0
        (cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ) := by
      rw [← hselect]
      exact (integral_map (by unfold cavityGaussianCoordinateMap; fun_prop)
        hF.aestronglyMeasurable).symm
    _ = _ := by
      rw [← hfield]
      exact integral_map (measurable_cavityReplicaField n T σ).aemeasurable
        hF.aestronglyMeasurable

end InvariantIsing

end

end OAI
