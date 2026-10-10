import OAI.Geometry.RCD.Heat.CanonicalRoughGaussianLower
import OAI.Geometry.RCD.Heat.CanonicalGaussianDifference

namespace OAI

/-! # A uniform short-time ratio for the actual heat kernel

The Gaussian upper/lower estimates and one local doubling comparison
control the earlier kernel everywhere by the later kernel at a fixed point.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_time_ratio :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ (t : ℝ), 0 < t → t ≤ 1/2 → ∀ x w z : X,
      hX.canonicalHeatKernel hn p t w z ≤
        A*Real.exp (D*(dist x z)^2/t)*hX.canonicalHeatKernel hn p (2*t) x z := by
  obtain ⟨C,B,hC,hB,hupper⟩ := hX.canonicalHeatKernel_upper_five hn p
  obtain ⟨c,E,hc,hE,hlower⟩ := hX.canonicalHeatKernel_rough_gaussian_lower hn p
  obtain ⟨J,hJ,hvol⟩ := hX.rescaled_ball_volume_factor hn (abs_nonneg K)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)
  let A := C*J/c*Real.exp B
  let D := E/2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨A,D,hA,hD,?_⟩
  intro t ht ht1 x w z
  have h2t : 0 < 2*t := by positivity
  have h2t1 : 2*t ≤ 1 := by linarith
  let V := (hausdorff n X).real (ball z (Real.sqrt t))
  let V₂ := (hausdorff n X).real (ball z (Real.sqrt (2*t)))
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport _ _ (Real.sqrt_pos.mpr ht)).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hV₂ : 0 < V₂ := ENNReal.toReal_pos (hX.fullSupport _ _ (Real.sqrt_pos.mpr h2t)).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hcurv : -|K| ≤ K*(Real.sqrt (2*t))^2 := by
    rw [Real.sq_sqrt h2t.le]
    have h₁ := mul_le_mul_of_nonneg_right (neg_abs_le K) h2t.le
    have h₂ := mul_le_mul_of_nonpos_left h2t1 (neg_nonpos.mpr (abs_nonneg K))
    nlinarith only [h₁,h₂]
  have hsmall : (1/2:ℝ)*Real.sqrt (2*t) ≤ Real.sqrt t := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg t)).mp
    rw [mul_pow,Real.sq_sqrt h2t.le,Real.sq_sqrt ht.le]
    nlinarith only [ht]
  have hVV : V₂ ≤ J*V := (hvol z _ (Real.sqrt_pos.mpr h2t) hcurv z (by
    rw [dist_self]; positivity)).trans (mul_le_mul_of_nonneg_left
      (measureReal_mono (ball_subset_ball hsmall) (hX.finiteOnBounded _ isBounded_ball).ne)
      (zero_le_one.trans hJ))
  have hu : hX.canonicalHeatKernel hn p t w z ≤ C/V*Real.exp B := by
    apply (hupper t ht w z).trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hC.le hV.le)
    apply Real.exp_le_exp.mpr
    have hd : 0 ≤ (dist w z)^2/(5*t) := by positivity
    have hBt : B*t ≤ B := by nlinarith only [hB,ht1]
    rw [neg_div]
    linarith
  let q := D*(dist x z)^2/t
  have hl : c/V₂*Real.exp (-q) ≤ hX.canonicalHeatKernel hn p (2*t) x z := by
    have hh := hlower (2*t) h2t h2t1 x z
    convert hh using 1
    congr 2
    dsimp only [q,D]
    ring
  have hcoef : C/V ≤ C*J/V₂ := by
    apply (div_le_div_iff₀ hV hV₂).mpr
    nlinarith only [hVV,hC]
  calc
    _ ≤ C/V*Real.exp B := hu
    _ ≤ C*J/V₂*Real.exp B := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos B).le
    _ = (A*Real.exp q)*(c/V₂*Real.exp (-q)) := by
      dsimp only [A]
      rw [Real.exp_neg]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg hA.le (Real.exp_pos q).le)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
