import OAI.MeasureTheory.Falconer.Graphs.GraphSliceDerivatives
import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeGradient
import OAI.MeasureTheory.Falconer.Estimates.LinearNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem compact_affine_phase_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Icc (-4:ℝ) 4) {C D τ : ℝ} (hτ : τ ≠ 0) (b : ℝ) (n : ℕ)
    (hb : ∀ z, ‖iteratedDeriv n f z‖ ≤ C*D^n) :
    ‖∫ z : ℝ, Complex.exp (Complex.I*((b+τ*z):ℂ))*f z‖ ≤ 8*C*D^n/|τ|^n := by
  let ξ := -τ/(2*Real.pi)
  have hξ : ξ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hτ) (by positivity)
  have he := compact_linear_phase_bound hf hs (by norm_num) hξ n hb
  have hphase (z : ℝ) : Complex.exp (Complex.I*((b+τ*z):ℂ))*f z =
      Complex.exp (Complex.I*(b:ℂ)) *
        (Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(z:ℂ)*(ξ:ℂ))*f z) := by
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    dsimp [ξ]
    push_cast
    field_simp
  simp_rw [hphase]
  rw [integral_const_mul,norm_mul]
  have hnorm : ‖Complex.exp (Complex.I*(b:ℂ))‖ = 1 := by
    rw [mul_comm Complex.I]
    exact Complex.norm_exp_ofReal_mul_I b
  rw [hnorm,one_mul]
  apply he.trans_eq
  have hd : (2*Real.pi)^n*‖ξ‖^n = |τ|^n := by
    rw [← mul_pow]
    congr 1
    dsimp [ξ]
    rw [abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    field_simp
  rw [hd]
  ring

theorem graph_z_nonstationary_bound {f : (Plane × ℝ) → ℂ} {C D : ℝ} (n : ℕ)
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (R s : ℝ) (v w η : Plane)
    (hτ : R*inner ℝ η (graphDerivative s v w) ≠ 0) :
    ‖∫ z : ℝ, Complex.exp (Complex.I*((R*inner ℝ η (graphA z v+s • graphB z w)):ℂ))*f (η,z)‖ ≤
      8*C*D^n/|R*inner ℝ η (graphDerivative s v w)|^n := by
  obtain ⟨hsm,hsupp,hder⟩ := hf.z_slice hs hC hD η
  have he := compact_affine_phase_bound hsm hsupp hτ
    (R*inner ℝ η ((1/2:ℝ) • (v+s • w))) n (hder n le_rfl)
  have hphase (z : ℝ) : R*inner ℝ η (graphA z v+s • graphB z w) =
      R*inner ℝ η ((1/2:ℝ) • (v+s • w)) + (R*inner ℝ η (graphDerivative s v w))*z := by
    simp only [graph_phase_affine,inner_add_right,real_inner_smul_right]
    ring
  simpa only [← Complex.ofReal_mul,← Complex.ofReal_add,hphase] using he

end PlanarFalconer

end OAI
