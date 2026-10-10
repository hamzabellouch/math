import Mathlib
import OAI.Geometry.WeakMTW.Analysis.SmoothFlow
import OAI.Geometry.WeakMTW.Geodesics.InitialScaling
import OAI.Geometry.WeakMTW.Coordinates.CoerciveMetric

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open GeodesicScaling

 theorem uniform_local_geodesics {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ y ∈ S, ∀ v : E, v ≠ 0 → 0 < G y v v)
    {x : E} (hx : x ∈ S) (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ S ∧
      ∀ y ∈ V, ∀ v : E, G y v v ≤ C ^ 2 →
        ∃ q : ℝ → E × E, q 0 = (y, v) ∧ ContDiffOn ℝ ∞ q (Metric.ball 0 ε) ∧
          ∀ t ∈ Metric.ball 0 ε, (q t).1 ∈ S ∧
            HasDerivAt q (geodesicSpray G (q t)) t := by
  obtain ⟨κ, hκ, V₀, hV₀, hxV₀, hV₀S, hcoer⟩ :=
    uniform_metric_coercive hS hG.continuousOn hx (hpos x hx)
  obtain ⟨W, Φ, hW, hmem, hΦ, hzero, hode⟩ := SmoothFlow.exists_smooth_local_flow
    (hS.prod isOpen_univ) (contDiffOn_geodesicSpray hS hG hpos)
    (x₀ := (x, (0 : E))) ⟨hx, mem_univ _⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hmem)
  let B : ℝ := 1 + C ^ 2 / κ
  have hB : 1 ≤ B := by
    have h := div_nonneg (sq_nonneg C) hκ.le
    dsimp [B]
    linarith
  let l : ℝ := r / (2 * (B + 1))
  have hl : 0 < l := div_pos hr (by linarith)
  have hleq : l * (2 * (B + 1)) = r := div_mul_cancel₀ _ (by linarith)
  let ε : ℝ := l * (r / 2)
  have hε : 0 < ε := mul_pos hl (half_pos hr)
  let V := V₀ ∩ Metric.ball x (r / 2)
  refine ⟨ε, hε, V, hV₀.inter Metric.isOpen_ball,
    ⟨hxV₀, Metric.mem_ball_self (half_pos hr)⟩, fun y hy => hV₀S hy.1, ?_⟩
  intro y hy v hv
  have hnv : ‖v‖ ^ 2 ≤ C ^ 2 / κ := (le_div_iff₀ hκ).mpr (by
    simpa only [mul_comm] using (hcoer y hy.1 v).trans hv)
  have hvB : ‖v‖ ≤ B := by
    have hb : B = 1 + C ^ 2 / κ := rfl
    nlinarith [sq_nonneg (‖v‖ - 1)]
  have hvl : ‖l • v‖ < r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    have hm := mul_le_mul_of_nonneg_left hvB hl.le
    nlinarith
  let q₀ : E × E := (y, l • v)
  have hdom : ∀ t ∈ Metric.ball (0 : ℝ) ε, (l⁻¹ * t, q₀) ∈ W := by
    intro t ht
    have hta : |t| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using ht
    have htl : |l⁻¹ * t| < r / 2 := by
      rw [abs_mul, abs_inv, abs_of_pos hl, inv_mul_eq_div]
      exact (div_lt_iff₀ hl).mpr (by simpa only [ε, mul_comm] using hta)
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, q₀,
      dist_zero_right, max_lt_iff]
    exact ⟨lt_trans htl (half_lt_self hr),
      lt_trans hy.2 (half_lt_self hr), lt_trans hvl (half_lt_self hr)⟩
  let q : ℝ → E × E := fun t => scalePhase l⁻¹ (Φ (l⁻¹ * t, q₀))
  have hq₀ : q 0 = (y, v) := by
    have hd := hdom 0 (Metric.mem_ball_self hε)
    simp only [mul_zero] at hd
    simp only [q, mul_zero, hzero q₀ hd, scalePhase_apply, q₀, smul_smul,
      inv_mul_cancel₀ hl.ne', one_smul]
  refine ⟨q, hq₀, ?_, ?_⟩
  · exact (scalePhase l⁻¹).contDiff.comp_contDiffOn
      (hΦ.comp ((contDiff_const.mul contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => l⁻¹ * t)).prodMk contDiff_const).contDiffOn hdom)
  · intro t ht
    have hd := (hode _ (hdom t ht)).2.scomp t ((hasDerivAt_id t).const_mul l⁻¹)
    have he := (scalePhase l⁻¹).hasFDerivAt.comp_hasDerivAt t hd
    refine ⟨(hode _ (hdom t ht)).1.1, ?_⟩
    convert! he using 1
    simp only [mul_one, scale_spray, q]

end
end CoordinateGeometry
end

end WeakMTWGlobalSupport

end OAI
