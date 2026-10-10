import OAI.Geometry.Riemannian.HarmonicCore.Model

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

structure AngularTensor where
  coeff : ℝ → E3 → M3
  smooth : ∀ (t : ℝ) (x : E3), x ≠ 0 → ∀ i j,
    ContDiffAt ℝ ∞ (fun p : ℝ × E3 ↦ coeff p.1 p.2 i j) (t, x)
  positive : ∀ t x, x ≠ 0 → (coeff t x).PosDef
  radial : ∀ t x, x ≠ 0 → coeff t x *ᵥ x.ofLp = x.ofLp
  homogeneous : ∀ t x (c : ℝ), 0 < c → coeff t (c • x) = coeff t x
  det_one : ∀ t x, x ≠ 0 → (coeff t x).det = 1
  round : ∀ t x, t ≤ 0 → coeff t x = 1



def radialProjection (x : E3) : M3 :=
  (‖x‖^2)⁻¹ • Matrix.vecMulVec x.ofLp x.ofLp



lemma radialProjection_posSemidef (x : E3) : (radialProjection x).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star x.ofLp
  simpa [radialProjection] using h.smul (inv_nonneg.mpr (sq_nonneg ‖x‖))



def polarCoeff (f : ℝ → ℝ) (H : AngularTensor) (x : E3) : M3 :=
  if x = 0 then 1 else
    (f ‖x‖ / ‖x‖)^2 • H.coeff (Real.log ‖x‖) x +
    (1 - (f ‖x‖ / ‖x‖)^2) • radialProjection x



lemma polarCoeff_core {f : ℝ → ℝ} (H : AngularTensor)
    (hf : ∀ r : ℝ, r ≤ 1 → f r = r) {x : E3} (hx : ‖x‖ ≤ 1) :
    polarCoeff f H x = 1 := by
  by_cases h0 : x = 0
  · simp [polarCoeff, h0]
  · have hn := norm_pos_iff.mpr h0
    rw [polarCoeff, ite_eq_right h0, hf _ hx, div_self hn.ne', one_pow,
      H.round _ _ (Real.log_nonpos hn.le hx)]
    simp



lemma polarCoeff_positive {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (H : AngularTensor)
    (hf : ∀ r : ℝ, 0 ≤ r → a * r ≤ f r ∧ f r ≤ r) (x : E3) :
    (polarCoeff f H x).PosDef := by
  by_cases hx : x = 0
  · simpa [polarCoeff, hx] using (Matrix.PosDef.one (n := Fin 3) (R := ℝ))
  have hn := norm_pos_iff.mpr hx
  have h := hf ‖x‖ hn.le
  have hq : 0 < f ‖x‖ / ‖x‖ := div_pos ((mul_pos ha hn).trans_le h.1) hn
  have hq1 : f ‖x‖ / ‖x‖ ≤ 1 := (div_le_one hn).2 h.2
  have hc : 0 ≤ 1 - (f ‖x‖ / ‖x‖)^2 := by nlinarith
  rw [polarCoeff, ite_eq_right hx]
  exact ((H.positive _ _ hx).smul (sq_pos_of_pos hq)).add_posSemidef
    ((radialProjection_posSemidef x).smul hc)



lemma radialProjection_smooth {x : E3} (hx : x ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y ↦ radialProjection y i j) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hi : ContDiff ℝ ∞ (fun y : E3 ↦ y i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hj : ContDiff ℝ ∞ (fun y : E3 ↦ y j) := (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  exact ((contDiffAt_norm ℝ hx).pow 2).inv (pow_ne_zero _ hn) |>.mul
    (hi.contDiffAt.mul hj.contDiffAt)



lemma polarCoeff_smooth {f : ℝ → ℝ} (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ polarCoeff f H x i j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E3) (by norm_num : (0 : ℝ) < 1)] with y hy
    have hy' : ‖y‖ ≤ 1 := by
      exact (show ‖y‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hy).le
    rw [polarCoeff_core H hc hy']
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnsm := contDiffAt_norm ℝ hx (n := ∞)
    have hq := ((hs.contDiffAt.comp x hnsm).div hnsm hn).pow 2
    have hh : ContDiffAt ℝ ∞ (fun y ↦ H.coeff (Real.log ‖y‖) y i j) x :=
      (H.smooth (Real.log ‖x‖) x hx i j).comp (f := fun y : E3 ↦ (Real.log ‖y‖, y)) x
        (((Real.contDiffAt_log.mpr hn).comp x hnsm).prodMk contDiffAt_id)
    apply ((hq.mul hh).add (((contDiffAt_const (c := (1 : ℝ))).sub hq).mul
      (radialProjection_smooth hx i j))).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [polarCoeff, hy, Matrix.add_apply, Matrix.smul_apply]



def polarMetric {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r) : SmoothMetric3 where
  coeff := polarCoeff f H
  smooth := polarCoeff_smooth H hs hc
  positive := polarCoeff_positive ha H hb



lemma polarMetric_euclidean {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (H : AngularTensor)
    (hs : ContDiff ℝ ∞ f) (hc : ∀ r : ℝ, r ≤ 1 → f r = r)
    (hb : ∀ r : ℝ, 0 ≤ r → a*r ≤ f r ∧ f r ≤ r) :
    (polarMetric ha f H hs hc hb).EuclideanNearOrigin := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx
  exact polarCoeff_core H hc hx.le

end HarmonicCounterexample.Main

end

end OAI
