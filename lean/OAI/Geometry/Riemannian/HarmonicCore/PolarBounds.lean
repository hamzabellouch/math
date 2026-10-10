import OAI.Geometry.Riemannian.HarmonicCore.PolarMetric
import OAI.Geometry.Riemannian.HarmonicCore.Completeness

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

lemma dotProduct_self_norm (x : E3) : x.ofLp ⬝ᵥ x.ofLp = ‖x‖^2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    real_inner_self_eq_norm_sq x



lemma radialProjection_mulVec {x : E3} (hx : x ≠ 0) :
    radialProjection x *ᵥ x.ofLp = x.ofLp := by
  rw [radialProjection, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_self_norm]
  ext i
  simp only [Pi.smul_apply, op_smul_eq_mul, smul_eq_mul]
  field_simp



lemma radialProjection_quad (x v : E3) :
    v.ofLp ⬝ᵥ (radialProjection x *ᵥ v.ofLp) =
      (inner ℝ x v)^2 / ‖x‖^2 := by
  rw [radialProjection, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_smul, dotProduct_comm,
    smul_eq_mul, sq, div_eq_mul_inv, mul_comm, mul_assoc]



lemma radialProjection_quad_bounds (x v : E3) :
    0 ≤ v.ofLp ⬝ᵥ (radialProjection x *ᵥ v.ofLp) ∧
      v.ofLp ⬝ᵥ (radialProjection x *ᵥ v.ofLp) ≤ ‖v‖^2 := by
  rw [radialProjection_quad]
  refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).2
    have h := pow_le_pow_left₀ (abs_nonneg (inner ℝ x v)) (abs_real_inner_le_norm x v) 2
    simpa [sq_abs, mul_pow, mul_comm] using h



lemma polarCoeff_radial (f : ℝ → ℝ) (H : AngularTensor) (x : E3) :
    polarCoeff f H x *ᵥ x.ofLp = x.ofLp := by
  by_cases hx : x = 0
  · simp [polarCoeff, hx]
  · rw [polarCoeff, ite_eq_right hx, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, H.radial _ _ hx, radialProjection_mulVec hx]
    module



def AngularBounds (H : AngularTensor) (c C : ℝ) : Prop :=
  ∀ t x, x ≠ 0 → ∀ v : E3,
    c^2 * ‖v‖^2 ≤ v.ofLp ⬝ᵥ (H.coeff t x *ᵥ v.ofLp) ∧
    v.ofLp ⬝ᵥ (H.coeff t x *ᵥ v.ofLp) ≤ C^2 * ‖v‖^2



lemma polarMetric_norm_bounds {a c C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hC1 : 1 ≤ C)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r)
    (hh : AngularBounds H c C) (x v : E3) :
    (a*c) * ‖v‖ ≤ Real.sqrt ((polarMetric ha f H hs hc hb).inner x v v) ∧
      Real.sqrt ((polarMetric ha f H hs hc hb).inner x v v) ≤ C * ‖v‖ := by
  let g := polarMetric ha f H hs hc hb
  have hp := g.inner_nonneg x v
  rw [Real.le_sqrt (mul_nonneg (mul_nonneg ha.le hc0.le) (norm_nonneg _)) hp,
    Real.sqrt_le_left (mul_nonneg (by linarith : 0 ≤ C) (norm_nonneg _))]
  rw [SmoothMetric3.inner_eq_dotProduct]
  change ((a*c)*‖v‖)^2 ≤ v.ofLp ⬝ᵥ (polarCoeff f H x *ᵥ v.ofLp) ∧
    v.ofLp ⬝ᵥ (polarCoeff f H x *ᵥ v.ofLp) ≤ (C*‖v‖)^2
  by_cases hx : x = 0
  · simp only [polarCoeff, ite_eq_left hx, Matrix.one_mulVec, dotProduct_self_norm, mul_pow]
    have hac : 0 ≤ a*c ∧ a*c ≤ 1 :=
      ⟨mul_nonneg ha.le hc0.le, (mul_le_mul ha1 hc1 hc0.le (by norm_num)).trans (by norm_num)⟩
    constructor <;> nlinarith [sq_nonneg ‖v‖,
      mul_nonneg (show 0 ≤ 1-(a*c)^2 by nlinarith) (sq_nonneg ‖v‖),
      mul_nonneg (show 0 ≤ C^2-1 by nlinarith) (sq_nonneg ‖v‖)]
  · have hn := norm_pos_iff.mpr hx
    have hw := hb ‖x‖ hn.le
    have hq0 : a ≤ f ‖x‖ / ‖x‖ := (le_div_iff₀ hn).2 hw.1
    have hq1 : f ‖x‖ / ‖x‖ ≤ 1 := (div_le_one hn).2 hw.2
    let q := (f ‖x‖ / ‖x‖)^2
    have hq : a^2 ≤ q ∧ q ≤ 1 := by dsimp [q]; constructor <;> nlinarith
    have hqp : 0 ≤ q := sq_nonneg _
    have hqc : 0 ≤ 1-q := by linarith
    have hA := hh (Real.log ‖x‖) x hx v
    have hP := radialProjection_quad_bounds x v
    rw [polarCoeff, ite_eq_right hx, Matrix.add_mulVec, dotProduct_add,
      Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul]
    change ((a*c)*‖v‖)^2 ≤ q * _ + (1-q) * _ ∧ _ ≤ (C*‖v‖)^2
    have hl := mul_le_mul_of_nonneg_left hA.1 hqp
    have hl' := mul_le_mul_of_nonneg_right hq.1 (mul_nonneg (sq_nonneg c) (sq_nonneg ‖v‖))
    have hpl := mul_nonneg hqc hP.1
    have hu := mul_le_mul_of_nonneg_left hA.2 hqp
    have hpu := mul_le_mul_of_nonneg_left hP.2 hqc
    have hu' := mul_nonneg hqc (mul_nonneg (show 0 ≤ C^2-1 by nlinarith) (sq_nonneg ‖v‖))
    constructor <;> dsimp only [smul_eq_mul] at * <;> nlinarith



lemma polarMetric_complete {a c C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hC1 : 1 ≤ C)
    (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r)
    (hh : AngularBounds H c C) :
    (polarMetric ha f H hs hc hb).Complete := by
  apply SmoothMetric3.complete_of_uniform_bounds _ (mul_pos ha hc0) (by linarith : 0 < C)
  exact polarMetric_norm_bounds ha ha1 hc0 hc1 hC1 f H hs hc hb hh

end HarmonicCounterexample.Main

end

end OAI
