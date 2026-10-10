import OAI.Probability.InvariantIsing.Cavity.CavityGroupGaussian
import OAI.Probability.InvariantIsing.Cavity.CavityProjectionLimit

namespace OAI

/-! Joint projections in the independent spectral groups. The output index
retains the group, replica, and fresh-axis coordinates, so the limiting
Gaussian law records independence between different groups. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGroupProjectionMatrix {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    Matrix (Fin m × (Fin r × Fin q)) ((a : Fin m) × (Fin (N a) × Fin q)) ℝ :=
  fun i j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then
    v j.1 i.2.1 j.2.1 / Real.sqrt (N j.1) else 0

def cavityGroupRawProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (x : Fin m → ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  (cavityGroupProjectionMatrix v).toEuclideanLin
    (WithLp.toLp 2 (fun j : (a : Fin m) × (Fin (N a) × Fin q) => x j.1 j.2.1 j.2.2))

lemma cavityGroupRawProjection_apply {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (x : Fin m → ℕ → Fin q → ℝ) (i : Fin m × (Fin r × Fin q)) :
    cavityGroupRawProjection v x i =
      ∑ k : Fin (N i.1), v i.1 i.2.1 k * cavityGaussianMatrix (x i.1) (N i.1) k i.2.2 := by
  classical
  change (∑ j : (a : Fin m) × (Fin (N a) × Fin q),
    cavityGroupProjectionMatrix v i j * x j.1 j.2.1 j.2.2) = _
  rw [Fintype.sum_sigma]
  simp only [cavityGroupProjectionMatrix, Fintype.sum_prod_type, ite_mul, zero_mul,
    ite_and]
  simp [cavityGaussianMatrix, div_mul_eq_mul_div, mul_div_assoc]

theorem cavityGroupRawProjection_hasLaw {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    HasLaw (cavityGroupRawProjection (q := q) v)
      (multivariateGaussian 0 (cavityGroupProjectionMatrix (q := q) v *
        (cavityGroupProjectionMatrix (q := q) v).transpose)) (cavityGroupGaussianRows m q) := by
  have hL : HasLaw (cavityGroupProjectionMatrix (q := q) v).toEuclideanLin.toContinuousLinearMap
      (multivariateGaussian 0 (cavityGroupProjectionMatrix (q := q) v *
        (cavityGroupProjectionMatrix (q := q) v).transpose))
      (stdGaussian (EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q)))) :=
    ⟨(by fun_prop), cavity_standardGaussian_image _⟩
  exact hL.fun_comp (cavityGroupGaussian_finite_standard_law N)

lemma cavityGroupGaussian_correction_measurable {m q : ℕ} (N : Fin m → ℕ) :
    Measurable (fun x : Fin m → ℕ → Fin q → ℝ =>
      fun a => (CFC.sqrt (cavityEmpiricalGram (x a) (N a)))⁻¹) := by
  apply Measurable.of_eval
  intro a
  exact (cavityGaussian_correction_measurable q (N a)).comp (measurable_pi_apply a)

lemma cavityGroupGaussian_correction_inMeasure {m q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop) :
    TendstoInMeasure (cavityGroupGaussianRows m q)
      (fun k x a => (CFC.sqrt (cavityEmpiricalGram (x a) (N k a)))⁻¹) atTop
      (fun _ _ => (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun k => (cavityGroupGaussian_correction_measurable (N k)).aestronglyMeasurable)
  have ha (a : Fin m) : ∀ᵐ x ∂cavityGroupGaussianRows m q,
      Tendsto (fun k => (CFC.sqrt (cavityEmpiricalGram (x a) (N k a)))⁻¹) atTop
        (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin m => cavityGaussianRows q) a).quasiMeasurePreserving.ae
      (cavityGaussian_correction_tendsto q)] with x hx
    exact hx.comp (hN a)
  filter_upwards [ae_all_iff.mpr ha] with x hx
  exact tendsto_pi_nhds.mpr hx

def cavityGroupCorrectProjection {m r q : ℕ}
    (y : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    (C : Fin m → Matrix (Fin q) (Fin q) ℝ) : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  WithLp.toLp 2 (fun i => ∑ j, y (i.1, i.2.1, j) * C i.1 j i.2.2)

@[simp] lemma cavityGroupCorrectProjection_one {m r q : ℕ}
    (y : EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    cavityGroupCorrectProjection y (fun _ => 1) = y := by
  ext i
  simp [cavityGroupCorrectProjection, Matrix.one_apply]

lemma continuous_cavityGroupCorrectProjection (m r q : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) ×
      (Fin m → Matrix (Fin q) (Fin q) ℝ) => cavityGroupCorrectProjection p.1 p.2) := by
  unfold cavityGroupCorrectProjection
  fun_prop

def cavityGroupFrameProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (x : Fin m → ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  WithLp.toLp 2 (fun i => ∑ k, v i.1 i.2.1 k *
    cavityNormalizeFrame (cavityGaussianMatrix (x i.1) (N i.1)) k i.2.2)

lemma cavityGroupCorrectProjection_raw {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) (x : Fin m → ℕ → Fin q → ℝ) :
    cavityGroupCorrectProjection (cavityGroupRawProjection v x)
      (fun a => (CFC.sqrt (cavityEmpiricalGram (x a) (N a)))⁻¹) =
      cavityGroupFrameProjection v x := by
  ext i
  change (∑ j, cavityGroupRawProjection v x (i.1, i.2.1, j) *
      ((CFC.sqrt (cavityEmpiricalGram (x i.1) (N i.1)))⁻¹) j i.2.2) = _
  simp_rw [cavityGroupRawProjection_apply]
  change (∑ j, (∑ k, v i.1 i.2.1 k *
      cavityGaussianMatrix (x i.1) (N i.1) k j) * _) = _
  simpa only [cavityCorrectProjection, cavityRawProjection_apply, cavityGroupFrameProjection]
    using cavityCorrectProjection_raw_apply (v i.1) (x i.1) i.2

theorem cavityGroupRawProjection_tendstoInDistribution {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (S : Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)
    (hS : S.PosSemidef)
    (hcov : Tendsto (fun k => cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose) atTop (𝓝 S)) :
    TendstoInDistribution (fun k => cavityGroupRawProjection (v k)) atTop id
      (fun _ => cavityGroupGaussianRows m q) (multivariateGaussian 0 S) := by
  refine ⟨fun k => (cavityGroupRawProjection_hasLaw (v k)).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  have hp (k : ℕ) : (cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (cavityGroupProjectionMatrix (q := q) (v k))
  have h := cavity_multivariateGaussian_weak_tendsto _ S hp hS hcov
  simp only [Measure.map_id]
  apply h.congr'
  filter_upwards [] with k
  apply Subtype.ext
  exact (cavityGroupRawProjection_hasLaw (v k)).map_eq.symm

/-- Joint normalization does not alter the multigroup Gaussian limit.
No independence between projections and their Gram corrections is needed. -/
theorem cavityGroupFrameProjection_tendstoInDistribution {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (S : Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)
    (hS : S.PosSemidef)
    (hcov : Tendsto (fun k => cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose) atTop (𝓝 S)) :
    TendstoInDistribution (fun k => cavityGroupFrameProjection (v k)) atTop id
      (fun _ => cavityGroupGaussianRows m q) (multivariateGaussian 0 S) := by
  have h := (cavityGroupRawProjection_tendstoInDistribution N v S hS hcov).continuous_comp_prodMk_of_tendstoInMeasure_const
      (continuous_cavityGroupCorrectProjection m r q)
      (cavityGroupGaussian_correction_inMeasure N hN)
      (fun k => (cavityGroupGaussian_correction_measurable (N k)).aemeasurable)
  simpa only [cavityGroupCorrectProjection_raw, cavityGroupCorrectProjection_one] using h

end InvariantIsing

end

end OAI
