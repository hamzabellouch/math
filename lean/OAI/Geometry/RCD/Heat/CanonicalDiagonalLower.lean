import OAI.Geometry.RCD.Heat.HeatOverlapDiagonalLower
import OAI.Geometry.RCD.Heat.HeatOverlapFinite
import OAI.Geometry.RCD.Coordinates.HeatNormalizationVolume

namespace OAI

/-! # Quantitative diagonal positivity of the canonical kernel

Conservation and the cutoff escape bound put half the heat mass in a
controlled ball. The already proved finiteness of the overlap converts
the extended Cauchy--Schwarz lower bound into a real one.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_short_diagonal_lower :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∀ (t : ℝ) (_ht : 0 < t), t ≤ r^2/C →
        (1/4 : ℝ)/(hausdorff n X).real (closedBall q (2*r)) ≤
          hX.canonicalHeatKernel hn p t q q := by
  obtain ⟨C,hC,hbound⟩ := hX.heatOverlapKernel_short_diagonal_lower hn p
  refine ⟨C,hC,?_⟩
  intro q r hr hcurv t ht htime
  have hhalf : t/2 ≤ r^2/(2*C) := by
    rw [show r^2/(2*C) = (r^2/C)/2 by ring]
    exact div_le_div_of_nonneg_right htime (by norm_num)
  have hb := hbound q r hr hcurv (t/2) (half_pos ht) hhalf
  have hh := ENNReal.toReal_mono (hX.heatOverlapKernel_finite hn p (t/2) (half_pos ht) q q) hb
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  simpa only [canonicalHeatKernel,dite_eq_left ht] using hh

theorem canonicalHeatKernel_diagonal_lower :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧ ∀ (t : ℝ), 0 < t → t ≤ τ → ∀ q : X,
      c/(hausdorff n X).real (ball q (Real.sqrt t)) ≤
        hX.canonicalHeatKernel hn p t q q := by
  obtain ⟨C,hC,hbound⟩ := hX.canonicalHeatKernel_short_diagonal_lower hn p
  let D := (6*Real.sqrt C*Real.exp 12)^n
  let τ := 1/(C*(|K|+1))
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hD : 0 < D := by dsimp only [D]; positivity
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  refine ⟨1/(4*D),τ,by positivity,hτ,?_⟩
  intro t ht htτ q
  let T := Real.sqrt t
  let r := Real.sqrt C*T
  have hT : 0 < T := Real.sqrt_pos.mpr ht
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr2 : r^2 = C*t := by dsimp only [r,T]; rw [mul_pow,Real.sq_sqrt hCpos.le,Real.sq_sqrt ht.le]
  have hcurv : -1 ≤ K*r^2 := by
    have hb : C*(|K|+1)*t ≤ 1 := by
      have hh := (le_div_iff₀ (by positivity : 0 < C*(|K|+1))).mp htτ
      nlinarith only [hh]
    have hk := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
    rw [hr2] at hk ⊢
    nlinarith only [hb,hk,mul_nonneg hCpos.le ht.le]
  have htime : t ≤ r^2/C := by rw [hr2,mul_div_cancel_left₀ t hCpos.ne']
  have hlower := hbound q r hr hcurv t ht htime
  let V := (hausdorff n X).real (ball q T)
  let W := (hausdorff n X).real (closedBall q (2*r))
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport q T hT).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hW : 0 < W := ENNReal.toReal_pos
    ((hX.fullSupport q (2*r) (by positivity)).trans_le (measure_mono ball_subset_closedBall)).ne'
      (hX.finiteOnBounded _ isBounded_closedBall).ne
  have hTr : T ≤ 3*r := by
    have hs : 1 ≤ Real.sqrt C := (Real.le_sqrt (by norm_num) hCpos.le).mpr (by simpa using hC)
    dsimp only [r]
    nlinarith only [mul_le_mul_of_nonneg_right hs hT.le,hT]
  have hv := hX.ball_volume_ratio_exp hn q q hT hTr (by simp; positivity : dist q q ≤ 3*r)
  have hsub : W ≤ (hausdorff n X).real (ball q (3*r)) :=
    measureReal_mono (closedBall_subset_ball (by linarith)) (hX.finiteOnBounded _ isBounded_ball).ne
  have hexp : Real.exp (4*Real.sqrt |K| *(3*r)) ≤ Real.exp 12 := by
    apply Real.exp_le_exp.mpr
    have hs : (Real.sqrt |K| *r)^2 ≤ 1 := by
      rw [mul_pow,Real.sq_sqrt (abs_nonneg K),hr2]
      have hb : C*(|K|+1)*t ≤ 1 := by
        have hh := (le_div_iff₀ (by positivity : 0 < C*(|K|+1))).mp htτ
        nlinarith only [hh]
      nlinarith only [hb,mul_nonneg hCpos.le ht.le]
    nlinarith only [hs,mul_nonneg (Real.sqrt_nonneg |K|) hr.le]
  have hcoef : (2*(3*r)/T*Real.exp (4*Real.sqrt |K| *(3*r)))^n ≤ D := by
    have he : 2*(3*r)/T = 6*Real.sqrt C := by dsimp only [r]; field_simp; ring
    rw [he]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hexp (by positivity)) n
  have hWV : W ≤ D*V := hsub.trans (hv.trans (mul_le_mul_of_nonneg_right hcoef hV.le))
  apply le_trans _ hlower
  change (1/(4*D))/V ≤ (1/4)/W
  apply (div_le_div_iff₀ hV hW).mpr
  field_simp
  linarith only [hWV]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
