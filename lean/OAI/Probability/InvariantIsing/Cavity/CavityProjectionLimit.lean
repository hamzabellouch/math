import OAI.Probability.InvariantIsing.Cavity.CavityGaussianProjection
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianContinuity
import OAI.Probability.InvariantIsing.Cavity.CavityFrameMeasurable

namespace OAI

/-! The Gram correction leaves the Gaussian projection limit unchanged.
The Slutsky step allows arbitrary dependence between the raw projections
and their normalizing Gram matrix. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityGaussian_correction_measurable (q n : ℕ) :
    Measurable (fun x : ℕ → Fin q → ℝ => (CFC.sqrt (cavityEmpiricalGram x n))⁻¹) :=
  cavity_matrix_inverse_measurable.comp
    (CFC.measurable_sqrt.comp (continuous_cavityEmpiricalGram q n).measurable)

lemma cavityGaussian_correction_inMeasure (q : ℕ) (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) :
    TendstoInMeasure (cavityGaussianRows q)
      (fun k x => (CFC.sqrt (cavityEmpiricalGram x (N k)))⁻¹) atTop
      (fun _ => (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun k => (cavityGaussian_correction_measurable q (N k)).aestronglyMeasurable)
  filter_upwards [cavityGaussian_correction_tendsto q] with x hx
  exact hx.comp hN

def cavityCorrectProjection {r q : ℕ}
    (y : EuclideanSpace ℝ (Fin r × Fin q)) (C : Matrix (Fin q) (Fin q) ℝ) :
    EuclideanSpace ℝ (Fin r × Fin q) :=
  WithLp.toLp 2 (fun a => ∑ j, y (a.1, j) * C j a.2)

@[simp] lemma cavityCorrectProjection_one {r q : ℕ}
    (y : EuclideanSpace ℝ (Fin r × Fin q)) : cavityCorrectProjection y 1 = y := by
  ext a
  simp [cavityCorrectProjection, Matrix.one_apply]

lemma continuous_cavityCorrectProjection (r q : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin r × Fin q) × Matrix (Fin q) (Fin q) ℝ =>
      cavityCorrectProjection p.1 p.2) := by
  unfold cavityCorrectProjection
  fun_prop

lemma cavityCorrectProjection_raw_apply {n r q : ℕ}
    (v : Fin r → Fin n → ℝ) (x : ℕ → Fin q → ℝ) (a : Fin r × Fin q) :
    cavityCorrectProjection (cavityRawProjection v x)
      ((CFC.sqrt (cavityEmpiricalGram x n))⁻¹) a =
      ∑ k : Fin n, v a.1 k * cavityNormalizeFrame (cavityGaussianMatrix x n) k a.2 := by
  change (∑ j, cavityRawProjection v x (a.1, j) *
      ((CFC.sqrt (cavityEmpiricalGram x n))⁻¹) j a.2) = _
  simp_rw [cavityRawProjection_apply]
  unfold cavityNormalizeFrame
  rw [cavityGaussianMatrix_gram]
  exact congrArg (fun M : Matrix (Fin r) (Fin q) ℝ => M a.1 a.2)
    (Matrix.mul_assoc v (cavityGaussianMatrix x n) ((CFC.sqrt (cavityEmpiricalGram x n))⁻¹))

theorem cavityRawProjection_tendstoInDistribution {r q : ℕ}
    (N : ℕ → ℕ) (v : (k : ℕ) → Fin r → Fin (N k) → ℝ)
    (S : Matrix (Fin r × Fin q) (Fin r × Fin q) ℝ) (hS : S.PosSemidef)
    (hcov : Tendsto (fun k => cavityProjectionMatrix (q := q) (v k) *
      (cavityProjectionMatrix (q := q) (v k)).transpose) atTop (𝓝 S)) :
    TendstoInDistribution (fun k => cavityRawProjection (v k)) atTop id
      (fun _ => cavityGaussianRows q) (multivariateGaussian 0 S) := by
  refine ⟨fun k => (cavityRawProjection_hasLaw (v k)).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  have hp (k : ℕ) : (cavityProjectionMatrix (q := q) (v k) *
      (cavityProjectionMatrix (q := q) (v k)).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose
      (cavityProjectionMatrix (q := q) (v k))
  have h := cavity_multivariateGaussian_weak_tendsto _ S hp hS hcov
  simp only [Measure.map_id]
  apply h.congr'
  filter_upwards [] with k
  apply Subtype.ext
  exact (cavityRawProjection_hasLaw (v k)).map_eq.symm

theorem cavityCorrectProjection_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (r q : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (X : ℕ → (ℕ → Fin q → ℝ) → EuclideanSpace ℝ (Fin r × Fin q))
    (Z : Ω → EuclideanSpace ℝ (Fin r × Fin q))
    (hX : TendstoInDistribution X atTop Z (fun _ => cavityGaussianRows q) ν) :
    TendstoInDistribution (fun k x => cavityCorrectProjection (X k x)
      ((CFC.sqrt (cavityEmpiricalGram x (N k)))⁻¹)) atTop Z
      (fun _ => cavityGaussianRows q) ν := by
  have h := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (continuous_cavityCorrectProjection r q) (cavityGaussian_correction_inMeasure q N hN)
    (fun k => (cavityGaussian_correction_measurable q (N k)).aemeasurable)
  simpa only [cavityCorrectProjection_one] using h

def cavityFrameProjection {n r q : ℕ} (v : Fin r → Fin n → ℝ)
    (x : ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin r × Fin q) :=
  WithLp.toLp 2 (fun a => ∑ k, v a.1 k *
    cavityNormalizeFrame (cavityGaussianMatrix x n) k a.2)

/-- The fixed number of normalized Gaussian directions has the same
Gaussian replica-projection limit as the unnormalized directions. -/
theorem cavityFrameProjection_tendstoInDistribution {r q : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (v : (k : ℕ) → Fin r → Fin (N k) → ℝ)
    (S : Matrix (Fin r × Fin q) (Fin r × Fin q) ℝ) (hS : S.PosSemidef)
    (hcov : Tendsto (fun k => cavityProjectionMatrix (q := q) (v k) *
      (cavityProjectionMatrix (q := q) (v k)).transpose) atTop (𝓝 S)) :
    TendstoInDistribution (fun k => cavityFrameProjection (v k)) atTop id
      (fun _ => cavityGaussianRows q) (multivariateGaussian 0 S) := by
  have h := cavityCorrectProjection_tendstoInDistribution
    (multivariateGaussian 0 S) r q N hN (fun k => cavityRawProjection (v k)) id
    (cavityRawProjection_tendstoInDistribution N v S hS hcov)
  convert h using 1
  funext k x
  ext a
  exact (cavityCorrectProjection_raw_apply (v k) x a).symm

def cavityReplicaCovariance {r : ℕ} (q : ℕ) (Q : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin r × Fin q) (Fin r × Fin q) ℝ :=
  fun a b => if a.2 = b.2 then Q a.1 b.1 else 0

lemma cavityProjection_covariance_tendsto {r q : ℕ}
    (N : ℕ → ℕ) (v : (k : ℕ) → Fin r → Fin (N k) → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k i j => (∑ l, v k i l * v k j l) / (N k : ℝ))
      atTop (𝓝 Q)) :
    Tendsto (fun k => cavityProjectionMatrix (q := q) (v k) *
      (cavityProjectionMatrix (q := q) (v k)).transpose) atTop
      (𝓝 (cavityReplicaCovariance q Q)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  simp only [cavityProjectionMatrix_covariance, cavityReplicaCovariance]
  by_cases hab : a.2 = b.2
  · simp only [ite_eq_left hab]
    exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ a.1)) b.1
  · simp only [ite_eq_right hab]
    exact tendsto_const_nhds

theorem cavityFrameProjection_tendsto_of_replicaGram {r q : ℕ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (v : (k : ℕ) → Fin r → Fin (N k) → ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k i j => (∑ l, v k i l * v k j l) / (N k : ℝ))
      atTop (𝓝 Q)) :
    TendstoInDistribution (fun k => cavityFrameProjection (q := q) (v k)) atTop id
      (fun _ => cavityGaussianRows q) (multivariateGaussian 0 (cavityReplicaCovariance q Q)) := by
  have hcov := cavityProjection_covariance_tendsto (q := q) N v Q hQ
  have hS : (cavityReplicaCovariance q Q).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall (fun k => by
      simpa using Matrix.posSemidef_self_mul_conjTranspose
        (cavityProjectionMatrix (q := q) (v k))))
  exact cavityFrameProjection_tendstoInDistribution N hN v _ hS hcov

end InvariantIsing

end

end OAI
