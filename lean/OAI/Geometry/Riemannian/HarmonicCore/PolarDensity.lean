import OAI.Geometry.Riemannian.HarmonicCore.RadialDistance

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main

lemma det_radial_update (A : M3) (x : E3) (d : ℝ)
    (hdet : A.det = 1) (hrad : A *ᵥ x.ofLp = x.ofLp) :
    (A + d • Matrix.vecMulVec x.ofLp x.ofLp).det = 1+d*‖x‖^2 := by
  have hunit : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hinv : A⁻¹ *ᵥ x.ofLp = x.ofLp := by
    calc
      A⁻¹ *ᵥ x.ofLp = A⁻¹ *ᵥ (A *ᵥ x.ofLp) := by rw [hrad]
      _ = (A⁻¹ * A) *ᵥ x.ofLp := Matrix.mulVec_mulVec _ _ _
      _ = x.ofLp := by rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  let U : Matrix (Fin 3) (Fin 1) ℝ := fun i _ ↦ d*x i
  let V : Matrix (Fin 1) (Fin 3) ℝ := fun _ i ↦ x i
  have hUV : U*V = d • Matrix.vecMulVec x.ofLp x.ofLp := by
    ext i j
    change (∑ k : Fin 1, (d*x i)*x j) = d*(x i*x j)
    simp [mul_assoc]
  have hU : A⁻¹ * U = U := by
    ext i j
    change (∑ k, A⁻¹ i k * (d*x k)) = d*x i
    calc
      _ = d * (A⁻¹ *ᵥ x.ofLp) i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = d*x i := by rw [hinv]
  rw [← hUV, Matrix.det_add_mul U V hunit, hdet, one_mul,
    Matrix.mul_assoc, hU, Matrix.det_fin_one]
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  congr 1
  change (∑ i, x i * (d*x i)) = d*‖x‖^2
  rw [← dotProduct_self_norm]
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring



lemma det_polar_algebra (A : M3) (x : E3) (q : ℝ)
    (hdet : A.det = 1) (hrad : A *ᵥ x.ofLp = x.ofLp)
    (hx : x ≠ 0) (hq : q ≠ 0) :
    (q • A + (1-q) • ((‖x‖^2)⁻¹ • Matrix.vecMulVec x.ofLp x.ofLp)).det = q^2 := by
  have hn : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hf : q • (A + ((1-q)/(q*‖x‖^2)) • Matrix.vecMulVec x.ofLp x.ofLp) =
      q • A + (1-q) • ((‖x‖^2)⁻¹ • Matrix.vecMulVec x.ofLp x.ofLp) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
  rw [← hf, Matrix.det_smul, det_radial_update _ _ _ hdet hrad]
  simp only [Fintype.card_fin]
  field_simp
  ring



lemma polarMetric_distance_origin {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r) (x : E3) :
    (polarMetric ha f H hs hc hb).distance 0 x = ‖x‖ := by
  apply SmoothMetric3.distance_origin_eq_norm
  · exact polarCoeff_radial f H
  · change polarCoeff f H 0 = 1
    simp [polarCoeff]



lemma polarMetric_density {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r) (x : E3) :
    Real.sqrt ((polarMetric ha f H hs hc hb).coeff x).det =
      if x = 0 then 1 else (f ‖x‖ / ‖x‖)^2 := by
  change Real.sqrt (polarCoeff f H x).det = _
  by_cases hx : x = 0
  · simp [polarCoeff, hx]
  · have hn := norm_pos_iff.mpr hx
    have hp : 0 < f ‖x‖ := (mul_pos ha hn).trans_le (hb ‖x‖ hn.le).1
    rw [ite_eq_right hx, polarCoeff, ite_eq_right hx, radialProjection,
      det_polar_algebra _ _ _ (H.det_one _ _ hx) (H.radial _ _ hx) hx
        (pow_ne_zero 2 (div_ne_zero hp.ne' hn.ne')),
      Real.sqrt_sq (sq_nonneg _)]



lemma polarMetric_density_bounds {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r) (x : E3) :
    a^2 ≤ Real.sqrt ((polarMetric ha f H hs hc hb).coeff x).det ∧
      Real.sqrt ((polarMetric ha f H hs hc hb).coeff x).det ≤ 1 := by
  rw [polarMetric_density]
  by_cases hx : x = 0
  · simp only [ite_eq_left hx]
    constructor <;> nlinarith
  · rw [ite_eq_right hx]
    have hn := norm_pos_iff.mpr hx
    have hw := hb ‖x‖ hn.le
    have h1 : a ≤ f ‖x‖ / ‖x‖ := (le_div_iff₀ hn).2 hw.1
    have h2 : f ‖x‖ / ‖x‖ ≤ 1 := (div_le_one hn).2 hw.2
    constructor <;> nlinarith

end HarmonicCounterexample.Main

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma density_continuous (g : SmoothMetric3) :
    Continuous (fun x ↦ Real.sqrt (g.coeff x).det) := by
  have h : Continuous g.coeff := continuous_pi (fun i ↦ continuous_pi
    (fun j ↦ (g.smooth i j).continuous))
  exact h.matrix_det.sqrt



lemma volumeMeasure_apply (g : SmoothMetric3) {s : Set E3} (hs : MeasurableSet s) :
    (g.volumeMeasure s).toReal = ∫ x in s, Real.sqrt (g.coeff x).det := by
  rw [volumeMeasure, withDensity_apply _ hs]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ ↦
    Real.sqrt_nonneg _)) g.density_continuous.aestronglyMeasurable).symm

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
