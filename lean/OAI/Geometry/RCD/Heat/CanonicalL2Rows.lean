import OAI.Geometry.RCD.Heat.CanonicalLocalBounds
import OAI.Geometry.RCD.Heat.HeatUniformTails
import OAI.Geometry.RCD.Sobolev.TightL2Difference

namespace OAI

/-! # Continuity of the canonical heat kernel through L² rows

Local kernel bounds and uniform square-integrable tails follow from the
actual RCD heat flow. Quantitative L¹ continuity then implies L²
continuity, and the half-time overlap is a continuous inner product.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_ae_radon (t : ℝ) (ht : 0 < t) (x : X) :
    hX.canonicalHeatKernel hn p t x =ᵐ[hausdorff n X]
      hX.heatRadonDensity hn p t ht x :=
  (hX.canonicalHeatKernel_ae hn p t ht x).trans (hX.heatJointDensity_ae hn p t ht x)

def canonicalL2Row
    (t : ℝ) (ht : 0 < t) (x : X) : Lp ℝ 2 (hausdorff n X) :=
  (hX.canonicalHeatKernel_memLp_two_unconditional hn p t ht x).toLp
    (hX.canonicalHeatKernel hn p t x)

theorem canonicalL2Row_coe
    (t : ℝ) (ht : 0 < t) (x : X) :
    hX.canonicalL2Row hn p t ht x =ᵐ[hausdorff n X] hX.canonicalHeatKernel hn p t x :=
  MemLp.coeFn_toLp _

theorem canonicalL2Row_integrable
    (t : ℝ) (ht : 0 < t) (x : X) :
    Integrable (hX.canonicalL2Row hn p t ht x) (hausdorff n X) :=
  (hX.canonicalHeatKernel_integrable hn p t ht x).congr
    (hX.canonicalL2Row_coe hn p t ht x).symm

theorem canonicalL2Row_continuous
    (t : ℝ) (ht : 0 < t) : Continuous (hX.canonicalL2Row hn p t ht) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨R,hR,htail⟩ := hX.heatRadonDensity_uniform_L2_tail hn p t ht x₀
    (ε := ε^2/16) (by positivity)
  obtain ⟨M,hM,hbound⟩ := hX.canonicalHeatKernel_bounded_on_ball hn p t ht x₀ R
  let L := Real.sqrt (1 / (2 * t * Real.exp (-2 * |K| * t)))
  let B := 2*M*L
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) hM) (Real.sqrt_nonneg _)
  refine ⟨min 1 (ε^2/(2*(B+1))), lt_min zero_lt_one (by positivity), ?_⟩
  intro x hx
  have hx1 : x ∈ ball x₀ 1 := mem_ball.mpr (hx.trans_le (min_le_left _ _))
  have hxR : x ∈ closedBall x₀ R := mem_closedBall.mpr ((mem_ball.mp hx1).le.trans hR)
  have hx₀R : x₀ ∈ closedBall x₀ R := mem_closedBall_self (zero_le_one.trans hR)
  have hloc (a : X) (ha : a ∈ closedBall x₀ R) :
      ∀ᵐ z ∂(hausdorff n X).restrict (closedBall x₀ R),
        |hX.canonicalL2Row hn p t ht a z| ≤ M := by
    filter_upwards [ae_restrict_of_ae (hX.canonicalL2Row_coe hn p t ht a),
      ae_restrict_mem measurableSet_closedBall] with z hz hzin
    rw [hz]
    exact hbound a ha z hzin
  have htailrow (a : X) (ha : a ∈ ball x₀ 1) :
      (∫ z in (closedBall x₀ R)ᶜ, (hX.canonicalL2Row hn p t ht a z)^2 ∂hausdorff n X) ≤ ε^2/16 := by
    have heq : (∫ z in (closedBall x₀ R)ᶜ, (hX.canonicalL2Row hn p t ht a z)^2 ∂hausdorff n X) =
        ∫ z in (closedBall x₀ R)ᶜ, (hX.heatRadonDensity hn p t ht a z)^2 ∂hausdorff n X := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hX.canonicalL2Row_coe hn p t ht a),
        ae_restrict_of_ae (hX.canonicalHeatKernel_ae_radon hn p t ht a)] with z hz hρ
      rw [hz,hρ]
    rw [heq]
    exact htail a ha
  have hsq := tight_L2_norm_sub_sq_le (hausdorff n X)
    (hX.canonicalL2Row hn p t ht x) (hX.canonicalL2Row hn p t ht x₀)
    (hX.canonicalL2Row_integrable hn p t ht x)
    (hX.canonicalL2Row_integrable hn p t ht x₀) measurableSet_closedBall hM
    (hloc x hxR) (hloc x₀ hx₀R)
  have he : (∫ z, |hX.canonicalL2Row hn p t ht x z -
      hX.canonicalL2Row hn p t ht x₀ z| ∂hausdorff n X) =
      ∫ z, |hX.heatRadonDensity hn p t ht x z - hX.heatRadonDensity hn p t ht x₀ z|
        ∂hausdorff n X := by
    apply integral_congr_ae
    filter_upwards [hX.canonicalL2Row_coe hn p t ht x,
      hX.canonicalL2Row_coe hn p t ht x₀,
      hX.canonicalHeatKernel_ae_radon hn p t ht x,
      hX.canonicalHeatKernel_ae_radon hn p t ht x₀] with z hx hx₀ hρ hρ₀
    rw [hx, hx₀, hρ, hρ₀]
  rw [he] at hsq
  have hprod := mul_le_mul_of_nonneg_left
    (hX.heatRadonDensity_integral_abs_sub_le hn p t ht x x₀)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hM)
  have ht1 := htailrow x hx1
  have ht0 := htailrow x₀ (mem_ball_self zero_lt_one)
  have hnorm : ‖hX.canonicalL2Row hn p t ht x - hX.canonicalL2Row hn p t ht x₀‖^2 ≤
      B*dist x x₀+ε^2/4 := by
    change _ ≤ (2*M)*(L*dist x x₀) at hprod
    dsimp only [B]
    nlinarith only [hsq,hprod,ht1,ht0]
  have hd : dist x x₀ < ε^2/(2*(B+1)) := hx.trans_le (min_le_right _ _)
  have hmul : dist x x₀*(2*(B+1)) < ε^2 := (lt_div_iff₀ (by positivity)).mp hd
  rw [dist_eq_norm]
  nlinarith [dist_nonneg (x := x) (y := x₀),
    norm_nonneg (hX.canonicalL2Row hn p t ht x - hX.canonicalL2Row hn p t ht x₀)]

theorem canonicalHeatKernel_eq_inner
    (t : ℝ) (ht : 0 < t) (x y : X) :
    hX.canonicalHeatKernel hn p t x y =
      inner ℝ (hX.canonicalL2Row hn p (t/2) (half_pos ht) x)
        (hX.canonicalL2Row hn p (t/2) (half_pos ht) y) := by
  rw [canonicalHeatKernel, dite_eq_left ht, hX.heatOverlapKernel_eq_lintegral hn p]
  rw [L2.inner_def]
  have he : (fun z => ENNReal.ofReal (hX.heatRadonDensity hn p (t/2) (half_pos ht) x z) *
      ENNReal.ofReal (hX.heatRadonDensity hn p (t/2) (half_pos ht) y z)) =ᵐ[hausdorff n X]
      fun z => ENNReal.ofReal
        (hX.canonicalL2Row hn p (t/2) (half_pos ht) x z *
          hX.canonicalL2Row hn p (t/2) (half_pos ht) y z) := by
    filter_upwards [hX.canonicalL2Row_coe hn p (t/2) (half_pos ht) x,
      hX.canonicalL2Row_coe hn p (t/2) (half_pos ht) y,
      hX.canonicalHeatKernel_ae_radon hn p (t/2) (half_pos ht) x,
      hX.canonicalHeatKernel_ae_radon hn p (t/2) (half_pos ht) y] with z hx hy hρ hσ
    rw [hx, hy, hρ, hσ, ENNReal.ofReal_mul (hX.heatRadonDensity_nonneg hn p _ _ x z)]
  rw [lintegral_congr_ae he]
  symm
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
    integral_eq_lintegral_of_nonneg_ae (μ := hausdorff n X)
      (f := fun z => hX.canonicalL2Row hn p (t/2) (half_pos ht) x z *
        hX.canonicalL2Row hn p (t/2) (half_pos ht) y z)
      (by
        filter_upwards [hX.canonicalL2Row_coe hn p (t/2) (half_pos ht) x,
          hX.canonicalL2Row_coe hn p (t/2) (half_pos ht) y] with z hx hy
        rw [hx, hy]
        exact mul_nonneg (hX.canonicalHeatKernel_nonneg hn p _ x z)
          (hX.canonicalHeatKernel_nonneg hn p _ y z))
      ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _))

theorem canonicalHeatKernel_continuous_joint
    (t : ℝ) (ht : 0 < t) :
    Continuous (fun xy : X × X => hX.canonicalHeatKernel hn p t xy.1 xy.2) := by
  have h := hX.canonicalL2Row_continuous hn p (t/2) (half_pos ht)
  simpa only [hX.canonicalHeatKernel_eq_inner hn p t ht, Function.comp_def] using!
    (h.comp continuous_fst).inner (h.comp continuous_snd)

theorem canonicalHeatKernel_continuous_right
    (t : ℝ) (ht : 0 < t) (x : X) : Continuous (hX.canonicalHeatKernel hn p t x) := by
  have h := (hX.canonicalHeatKernel_continuous_joint hn p t ht).comp
    (show Continuous (fun y : X => (x, y)) from continuous_const.prodMk continuous_id)
  simpa only [Function.comp_def] using! h

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
