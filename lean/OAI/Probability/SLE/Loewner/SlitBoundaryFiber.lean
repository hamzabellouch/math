import OAI.Probability.SLE.Geometry.HalfPlaneBoundaryIdentity
import OAI.Probability.SLE.Loewner.SlitChartBoundaryExtension

namespace OAI

/-! No interval of real boundary parameters collapses to a single point
under the continuous inverse slit chart. -/
noncomputable section
open Set Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma vertical_point_mem_ball (x : ℝ) {y r : ℝ} (hy : 0<y) (hyr : y<r) :
    (x:ℂ)+(y:ℂ)*I∈ball (x:ℂ) r := by
  simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,norm_real,
    Real.norm_eq_abs,abs_of_pos hy,norm_I,mul_one] using hyr

theorem SimpleSlitChart.boundary_not_constant_on_interval {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) {Fbar : ℂ → ℂ}
    (hC : ContinuousOn Fbar {z : ℂ | 0≤z.im})
    (he : ∀ z∈upperHalfPlane, Fbar z=P.inverse z)
    (x : ℝ) {r : ℝ} (hr : 0<r) (c : ℂ) :
    ¬ ∀ y∈Ioo (x-r) (x+r), Fbar (y:ℂ)=c := by
  intro hconst
  have hd : DifferentiableOn ℂ Fbar upperHalfPlane :=
    P.inverse_differentiable.congr (fun z hz => he z hz)
  have hlocal := halfPlane_boundary_identity hC hd x hr c (fun z hz hzi => by
    have hre : |z.re-x|<r := lt_of_le_of_lt
      (by simpa only [sub_re,ofReal_re,dist_eq_norm] using Complex.abs_re_le_norm (z-(x:ℂ))) hz
    have hxr := abs_lt.mp hre
    have hez : z=(z.re:ℂ) := by apply Complex.ext <;> simp [hzi]
    rw [hez]
    exact hconst z.re ⟨by linarith,by linarith⟩)
  let z₁ : ℂ := (x:ℂ)+((r/2:ℝ):ℂ)*I
  let z₂ : ℂ := (x:ℂ)+((r/3:ℝ):ℂ)*I
  have hz₁ : z₁∈upperHalfPlane := by
    change 0<z₁.im
    dsimp [z₁]
    simpa using half_pos hr
  have hz₂ : z₂∈upperHalfPlane := by
    change 0<z₂.im
    dsimp [z₂]
    simpa using div_pos hr (by norm_num : (0:ℝ)<3)
  have hb₁ : z₁∈ball (x:ℂ) r := vertical_point_mem_ball x (half_pos hr) (by linarith)
  have hb₂ : z₂∈ball (x:ℂ) r := vertical_point_mem_ball x
    (div_pos hr (by norm_num : (0:ℝ)<3)) (by linarith)
  have hv₁ := hlocal z₁ hb₁ hz₁
  have hv₂ := hlocal z₂ hb₂ hz₂
  rw [he z₁ hz₁] at hv₁
  rw [he z₂ hz₂] at hv₂
  have heq := P.inverse_injOn hz₁ hz₂ (hv₁.trans hv₂.symm)
  have him := congrArg Complex.im heq
  dsimp [z₁,z₂] at him
  simp only [ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at him
  linarith

end SLEExactGauge

end

end OAI
