import OAI.MeasureTheory.Falconer.Fourier.PlaneFourierNonstationary
import OAI.MeasureTheory.Falconer.Graphs.GraphZIntegratedNonedge

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff FourierTransform

theorem plane_compact_linear_phase_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Metric.closedBall (0:Plane) 8) (n : ℕ) {C D : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*D^n) (q : Plane) (hq : q ≠ 0) :
    ‖∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal (inner ℝ η q))*f η‖ ≤
      (C*D^n*volume.real (Metric.closedBall (0:Plane) 8))/‖q‖^n := by
  let ξ := (-(2*Real.pi)⁻¹) • q
  have hξ : ξ ≠ 0 := smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by positivity))) hq
  have he := plane_compact_fourier_bound hf hs n hb ξ hξ
  have hphase : 𝓕 f ξ = ∫ η : Plane,
      Complex.exp (Complex.I*Complex.ofReal (inner ℝ η q))*f η := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with η
    simp only [ξ,real_inner_smul_right,smul_eq_mul]
    congr 2
    push_cast
    field_simp
  rw [hphase] at he
  have hd : (2*Real.pi)^n*‖ξ‖^n = ‖q‖^n := by
    rw [← mul_pow]
    congr 1
    simp [ξ,norm_smul,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    field_simp
  simpa only [hd] using he

theorem graph_eta_slice_derivative_le {f : (Plane × ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (η : Plane) (z : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun e => f (e,z)) η‖ ≤ ‖iteratedFDeriv ℝ n f (η,z)‖ := by
  let g : (Plane × ℝ) → ℂ := fun p => f (p+(0,z))
  let L : Plane →L[ℝ] (Plane × ℝ) := ContinuousLinearMap.inl ℝ Plane ℝ
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun e => f (e,z)) = g ∘ L := by funext e; simp [g,L]
  rw [he,L.iteratedFDeriv_comp_right hg η (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hn : ‖L‖ = 1 := ContinuousLinearMap.norm_inl ℝ Plane ℝ
  simp only [hn,Finset.prod_const_one,mul_one]
  dsimp only [g]
  rw [iteratedFDeriv_comp_add_right]
  simp [L]

theorem graph_eta_nonstationary_bound {f : (Plane × ℝ) → ℂ} {C D : ℝ} (n : ℕ)
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (R s z : ℝ) (x y : Plane)
    (hq : R • (graphA z x+s • graphB z y) ≠ 0) :
    ‖∫ η : Plane, Complex.exp (Complex.I*Complex.ofReal
      (R*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      (C*D^n*volume.real (Metric.closedBall (0:Plane) 8))/
        ‖R • (graphA z x+s • graphB z y)‖^n := by
  have hg := hf.global_smooth hs
  have hs' : tsupport (fun η => f (η,z)) ⊆ Metric.closedBall (0:Plane) 8 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro η hη
    exact (hs (subset_closure hη)).1.1
  have he := plane_compact_linear_phase_bound
    (hg.comp (contDiff_id.prodMk contDiff_const)) hs' n
    (fun η => (graph_eta_slice_derivative_le hg η z n).trans
      (hf.global_bound hs hC hD n le_rfl (η,z)))
    (R • (graphA z x+s • graphB z y)) hq
  simpa only [real_inner_smul_right, Function.comp_apply, id_eq] using he

end PlanarFalconer

end OAI
