import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowPositiveRay
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Differentiating the Euler representation in the spatial parameter -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem norm_slowEulerKernel (q : ℂ) (m : ℕ) (x : ℂ) {v : ℝ} (hv : 0 < v) :
    ‖slowEulerKernel q m x v‖ = Real.exp (-x.re * v) * v ^ (q.re - 1) *
      (1 + v) ^ ((m : ℝ) - 1 - q.re) := by
  have hbase : (1 : ℂ) + (v : ℂ) = ((1 + v : ℝ) : ℂ) := by push_cast; rfl
  rw [slowEulerKernel, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hv,
    hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + v)]
  simp

theorem norm_slowEulerKernel_le (q : ℂ) (m : ℕ) (x : ℂ) (c : ℝ)
    (hx : c ≤ x.re) {v : ℝ} (hv : 0 < v) :
    ‖slowEulerKernel q m x v‖ ≤ ‖slowEulerKernel q m (c : ℂ) v‖ := by
  rw [norm_slowEulerKernel q m x hv, norm_slowEulerKernel q m (c : ℂ) hv,
    Complex.ofReal_re]
  gcongr

theorem continuousOn_slowEulerKernel (q : ℂ) (m : ℕ) (x : ℂ) :
    ContinuousOn (slowEulerKernel q m x) (Set.Ioi 0) := by
  have h₁ : ContinuousOn (fun v : ℝ => (v : ℂ) ^ (q - 1)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (fun v hv =>
      Complex.ofReal_mem_slitPlane.mpr hv)
  have h₂ : ContinuousOn
      (fun v : ℝ => (1 + (v : ℂ)) ^ ((m : ℂ) - 1 - q)) (Set.Ioi 0) := by
    apply (continuous_const.add Complex.continuous_ofReal).continuousOn.cpow_const
    intro v hv
    apply Complex.mem_slitPlane_iff.mpr
    left
    change 0 < 1 + v
    linarith [show 0 < v from hv]
  exact (show ContinuousOn (fun v : ℝ => Complex.exp (-x * (v : ℂ))) (Set.Ioi 0) by
    fun_prop).mul h₁ |>.mul h₂

theorem integrable_slowEulerKernel (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    IntegrableOn (slowEulerKernel q m x) (Set.Ioi 0) := by
  apply (integrable_slowEulerKernel_real q m hq hx).norm.mono'
    ((continuousOn_slowEulerKernel q m x).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact norm_slowEulerKernel_le q m x x.re le_rfl hv

theorem hasDerivAt_slowEulerKernel (q : ℂ) (m : ℕ) (x : ℂ) {v : ℝ}
    (hv : 0 < v) :
    HasDerivAt (fun z : ℂ => slowEulerKernel q m z v)
      (-slowEulerKernel (q + 1) (m + 1) x v) x := by
  have hp : (v : ℂ) ^ (q - 1) * (v : ℂ) = (v : ℂ) ^ q := by
    calc
      (v : ℂ) ^ (q - 1) * (v : ℂ) = (v : ℂ) ^ (q - 1) * (v : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = (v : ℂ) ^ (q - 1 + 1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
      _ = (v : ℂ) ^ q := by congr 1; ring
  have hm : ((m + 1 : ℕ) : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q := by push_cast; ring
  have he : HasDerivAt (fun z : ℂ => Complex.exp (-z * (v : ℂ)))
      (Complex.exp (-x * (v : ℂ)) * (-(v : ℂ))) x := by
    simpa only [Pi.neg_apply, id_eq, neg_one_mul] using
      (((hasDerivAt_id x).neg).mul_const (v : ℂ)).cexp
  convert! he.mul_const ((v : ℂ) ^ (q - 1) *
    (1 + (v : ℂ)) ^ ((m : ℂ) - 1 - q)) using 1
  · funext z
    dsimp only [slowEulerKernel]
    ring
  · simp only [slowEulerKernel, hm, add_sub_cancel_right]
    rw [← hp]
    ring

/-- Differentiation under the Euler integral in its initial half-plane. -/
theorem hasDerivAt_integral_slowEulerKernel (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    HasDerivAt (fun z : ℂ => ∫ v : ℝ in Set.Ioi 0, slowEulerKernel q m z v)
      (-(∫ v : ℝ in Set.Ioi 0, slowEulerKernel (q + 1) (m + 1) x v)) x := by
  let c : ℝ := x.re / 2
  let s : Set ℂ := {z | c < z.re}
  have hc : 0 < c := half_pos hx
  have hs : s ∈ 𝓝 x := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by dsimp [s, c]; linarith)
  have hq' : 0 < (q + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun z v => slowEulerKernel q m z v)
    (F' := fun z v => -slowEulerKernel (q + 1) (m + 1) z v)
    (bound := fun v => ‖slowEulerKernel (q + 1) (m + 1) (c : ℂ) v‖) hs
    (Filter.Eventually.of_forall fun z =>
      (continuousOn_slowEulerKernel q m z).aestronglyMeasurable measurableSet_Ioi)
    (integrable_slowEulerKernel q m x hq hx)
    ((continuousOn_slowEulerKernel (q + 1) (m + 1) x).aestronglyMeasurable
      measurableSet_Ioi).neg
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      intro z hz
      rw [norm_neg]
      exact norm_slowEulerKernel_le (q + 1) (m + 1) z c (le_of_lt hz) hv)
    (integrable_slowEulerKernel_real (q + 1) (m + 1) hq' hc).norm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      intro z _
      exact hasDerivAt_slowEulerKernel q m z hv)
  simpa only [integral_neg] using hd.2

end DefocusingNLS

end OAI
