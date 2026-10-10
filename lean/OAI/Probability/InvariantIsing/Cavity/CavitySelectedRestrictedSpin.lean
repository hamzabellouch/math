import OAI.Probability.InvariantIsing.Cavity.CavitySelectedCappedSpin
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedSpinTest

namespace OAI

/-! The selected finite Gaussian field preserves the hard replica
cutoff, as well as its capped spin factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityRestrictedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ B : ℝ) (π : Measure (Spin k))
    (F : (Fin r → Spin k) → ℝ) (y : EuclideanSpace ℝ (Fin r × Fin d)) : ℝ :=
  if ∀ i, 1+‖(WithLp.toLp 2 (fun a => y (i,a)) : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2
  then cavityCappedFlatSpinValue K L C τ π F y else 0

lemma measurable_cavityRestrictedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ B : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) :
    Measurable (cavityRestrictedFlatSpinValue K L C τ B π F) := by
  apply Measurable.ite _ (measurable_cavityCappedFlatSpinValue K L C τ π F) measurable_const
  have he : {y : EuclideanSpace ℝ (Fin r × Fin d) |
      ∀ i, 1+‖(WithLp.toLp 2 (fun a => y (i,a)) : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2} =
      ⋂ i : Fin r, {y | 1+‖(WithLp.toLp 2 (fun a => y (i,a)) :
        EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2} := by ext y; simp
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le _ measurable_const
  fun_prop

lemma cavity_restricted_selected_eq_flat {m r d k q : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (e : Fin d → Fin m × Fin q) (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (block : SpectralBlock m r) (z : EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    cavityRestrictedSpinReplicaValue K L C τ B (cavitySelectedGroupProjection e) π F (block,z) =
      cavityRestrictedFlatSpinValue K L C τ B π (fun ε => F (block,ε))
        (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e) z) := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C τ hB]
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  simp only [cavityReplicaRadius_le_iff _ _ hB,cavity_capped_selected_eq_flat]
  rfl

theorem cavity_selected_restricted_spin_test {m d n r k qdim : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin qdim)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (T : LabeledTree n) (σ : Fin r → LabeledLeaf n)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) {Bcut : ℝ} (hBcut : 0 ≤ Bcut) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    let B := cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ
    (∫ z, cavityRestrictedSpinReplicaValue K L C τ Bcut (cavitySelectedGroupProjection e) π F (B, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance qdim rho B)) =
      ∫ z, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B, ε))
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
  simp_rw [cavity_restricted_selected_eq_flat K L C τ hBcut]
  exact cavity_selected_group_gaussian_test rho lam hrho hsum g e he heg p cut hcut hfirst hlast
    q hq hp htop T σ _ (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π _)

end InvariantIsing

end

end OAI
