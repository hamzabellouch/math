import OAI.Probability.SLE.Geometry.CircleRadialFlux
import OAI.Probability.SLE.Geometry.AnnulusPolarIntegral

namespace OAI

/-! A lower bound on circle averages of a Laplacian integrates to a
quadratic lower bound on boundary flux. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian

namespace SLEExactGauge

lemma radial_flux_ge_of_circle_laplacian {u : ℂ → ℝ} {R C : ℝ} (hR : 0<R)
    (hu : ∀ z∈closedBall (0:ℂ) R, ContDiffAt ℝ 2 u z)
    (havg : ∀ r∈Icc 0 R, C≤circleAverage (Δ u) 0 r) :
    Real.pi*C*R^2≤∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (R,θ) := by
  let F (r : ℝ) := ∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (r,θ)
  let G (r : ℝ) := ∫ θ in -Real.pi..Real.pi, r*(Δ u) (polarPoint r θ)
  have hGc : ContinuousOn G (Icc 0 R) := by
    have hc : ContinuousOn (Δ u) {z : ℂ | ‖z-(0:ℂ)‖∈Icc 0 R} := by
      intro z hz
      exact (plane_laplacian_continuousAt (hu z (by
        rw [mem_closedBall,dist_eq_norm]; exact hz.2))).continuousWithinAt
    have hh := hc.circleAverage (fun r hr => hr.1)
    apply ((continuousOn_const.mul continuousOn_id).mul hh).congr
    intro r _
    exact polar_integral_eq_circleAverage (Δ u) r
  have hlower {a : ℝ} (ha : 0<a) (haR : a≤R) :
      Real.pi*C*(R^2-a^2)≤F R-F a := by
    have hiG : IntervalIntegrable G volume a R :=
      (hGc.mono (Icc_subset_Icc ha.le le_rfl)).intervalIntegrable_of_Icc haR
    have hil : IntervalIntegrable (fun r : ℝ => 2*Real.pi*C*r) volume a R := by
      exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hib := intervalIntegral.integral_mono_on haR hil hiG (fun r hr => by
      dsimp only [G]
      rw [polar_integral_eq_circleAverage]
      have hh := mul_le_mul_of_nonneg_left (havg r ⟨ha.le.trans hr.1,hr.2⟩)
        (mul_nonneg (by positivity : 0≤2*Real.pi) (ha.le.trans hr.1))
      nlinarith only [hh])
    have hprimitive (r : ℝ) :
        HasDerivAt (fun r : ℝ => Real.pi*C*r^2) (2*Real.pi*C*r) r := by
      convert! (hasDerivAt_pow 2 r).const_mul (Real.pi*C) using 1; ring
    have heil : (∫ r in a..R, 2*Real.pi*C*r)=Real.pi*C*(R^2-a^2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hprimitive r) hil]
      ring
    have heig : (∫ r in a..R, G r)=F R-F a :=
      annulus_laplacian_flux ha haR (fun z _ hzR => hu z (by
        rw [mem_closedBall,dist_zero_right]; exact hzR))
    rwa [heil,heig] at hib
  let a (n : ℕ) := R*greenInner n
  have han (n : ℕ) : a n∈Ioc 0 R := by
    constructor
    · exact mul_pos hR (greenInner_pos n)
    · have hh := mul_le_mul_of_nonneg_left (greenInner_le_half n) hR.le
      dsimp only [a]
      linarith
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a,mul_zero] using greenInner_tendsto.const_mul R
  have haT : Tendsto a atTop (𝓝[Icc 0 R] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hat,Eventually.of_forall (fun n => ⟨(han n).1.le,(han n).2⟩)⟩
  have hFt : Tendsto (fun n => F (a n)) atTop (𝓝 0) := by
    have hh := (radial_flux_continuousOn hu 0 ⟨le_rfl,hR.le⟩).tendsto.comp haT
    simpa only [F,Function.comp_def,radial_flux_zero] using hh
  have hlim : Tendsto (fun n => F (a n)+Real.pi*C*(R^2-(a n)^2)) atTop
      (𝓝 (Real.pi*C*R^2)) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,zero_add] using
      hFt.add ((tendsto_const_nhds.sub (hat.pow 2)).const_mul (Real.pi*C))
  exact le_of_tendsto hlim (Eventually.of_forall (fun n => by
    have hh := hlower (han n).1 (han n).2
    linarith))

end SLEExactGauge

end

end OAI
