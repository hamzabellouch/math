import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OAI

/-!
# Rigidity of the Euler equation on a ball

The Euclidean limit in the sharp projection argument satisfies an Euler
equation with affine forcing.  Two derivatives suffice to force the limit
to be affine; harmonic analyticity is not needed for this step.
-/

open Set Filter
open scoped Topology

namespace RegularPointCoordinates

/-- A continuous function constant immediately to the right has the same
value at the endpoint. -/
theorem eq_zero_of_continuousAt_eq_on_Ioo {g : ℝ → ℝ} {c R : ℝ}
    (hR : 0 < R) (hg : ContinuousAt g 0)
    (heq : ∀ t ∈ Ioo 0 R, g t = c) : g 0 = c := by
  have hevent : g =ᶠ[𝓝[>] 0] fun _ => c := by
    filter_upwards [Ioo_mem_nhdsGT hR] with t ht
    exact heq t ht
  exact tendsto_nhds_unique_of_eventuallyEq
    (hg.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hevent

/-- Differentiating the scalar Euler equation cancels the first derivatives. -/
theorem scalar_euler_derivative {f f' f'' : ℝ → ℝ} {ell k R t : ℝ}
    (ht : t ∈ Ioo (-R) R)
    (hf : HasDerivAt f (f' t) t) (hf' : HasDerivAt f' (f'' t) t)
    (heuler : ∀ s ∈ Ioo (-R) R, s * f' s = f s + ell * s + k) :
    t * f'' t = ell := by
  have hevent : (fun s => s * f' s) =ᶠ[𝓝 t]
      (fun s => f s + ell * s + k) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact heuler s hs
  have hleft := (hasDerivAt_id t).mul hf'
  have hright := (hf.add ((hasDerivAt_id t).const_mul ell)).add_const k
  have heq := (hleft.congr_of_eventuallyEq hevent.symm).unique hright
  dsimp at heq
  linarith

/-- A twice differentiable scalar ray satisfying the affine-forced Euler
equation has zero linear forcing and the affine value at time one. -/
theorem scalar_euler_ray_affine {f f' f'' : ℝ → ℝ} {ell k R : ℝ}
    (hR : 1 < R)
    (hf : ∀ t ∈ Ioo (-R) R, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo (-R) R, HasDerivAt f' (f'' t) t)
    (heuler : ∀ t ∈ Ioo (-R) R, t * f' t = f t + ell * t + k) :
    ell = 0 ∧ k = -f 0 ∧ f 1 = f 0 + f' 0 := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hRpos⟩
  have hone : (1 : ℝ) ∈ Ioo 0 R := ⟨zero_lt_one, hR⟩
  have hell : ell = 0 := by
    have := scalar_euler_derivative hzero (hf 0 hzero) (hf' 0 hzero) heuler
    simpa using this.symm
  have hk : k = -f 0 := by
    have := heuler 0 hzero
    simp only [zero_mul, mul_zero, add_zero] at this
    linarith
  have hsecond : ∀ t ∈ Ioo 0 R, f'' t = 0 := by
    intro t ht
    have h := scalar_euler_derivative ⟨by linarith [ht.1], ht.2⟩
      (hf t ⟨by linarith [ht.1], ht.2⟩) (hf' t ⟨by linarith [ht.1], ht.2⟩) heuler
    rw [hell] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt ht.1)
  have hconst : ∀ t ∈ Ioo 0 R, f' t = f' 1 := by
    intro t ht
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 R).isPreconnected
      (fun s hs => (hf' s ⟨by linarith [hs.1], hs.2⟩).differentiableAt.differentiableWithinAt)
      (fun s hs => ?_) ht hone
    rw [(hf' s ⟨by linarith [hs.1], hs.2⟩).deriv, hsecond s hs]
    rfl
  have hfirst0 : f' 0 = f' 1 :=
    eq_zero_of_continuousAt_eq_on_Ioo hRpos (hf' 0 hzero).continuousAt hconst
  have hvalue : ∀ t ∈ Ioo 0 R, f t - t * f' 1 = f 1 - f' 1 := by
    intro t ht
    have hderiv : ∀ s ∈ Ioo 0 R,
        HasDerivAt (fun s => f s - s * f' 1) 0 s := by
      intro s hs
      have h := (hf s ⟨by linarith [hs.1], hs.2⟩).sub
        ((hasDerivAt_id s).mul_const (f' 1))
      change HasDerivAt (fun s => f s - s * f' 1) (f' s - 1 * f' 1) s at h
      simpa only [one_mul, hconst s hs, sub_self] using h
    have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 R).isPreconnected
      (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hderiv s hs).deriv) ht hone
    simpa using h
  have hvalue0 : f 0 = f 1 - f' 1 := by
    have hcont : ContinuousAt (fun t => f t - t * f' 1) 0 :=
      (hf 0 hzero).continuousAt.sub (continuousAt_id.mul continuousAt_const)
    simpa using eq_zero_of_continuousAt_eq_on_Ioo hRpos hcont hvalue
  exact ⟨hell, hk, by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At the origin, differentiating the Euler equation forces its linear
forcing to vanish.  The derivative of the radial factor cancels `Dw 0`. -/
theorem euler_linear_forcing_eq_zero {w : E → ℝ}
    {Dw : E → E →L[ℝ] ℝ} {DDw : E →L[ℝ] (E →L[ℝ] ℝ)}
    {ell : E →L[ℝ] ℝ} {k R : ℝ} (hR : 0 < R)
    (hw : HasFDerivAt w (Dw 0) 0) (hDw : HasFDerivAt Dw DDw 0)
    (heuler : ∀ x ∈ Metric.ball 0 R, Dw x x = w x + ell x + k) :
    ell = 0 := by
  have hevent : (fun x => Dw x x) =ᶠ[𝓝 0] (fun x => w x + ell x + k) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hR] with x hx
    exact heuler x hx
  have hleft := hDw.clm_apply (hasFDerivAt_id (0 : E))
  have hright := (hw.add ell.hasFDerivAt).add_const k
  have hlin : Dw 0 = Dw 0 + ell := by
    simpa using (hleft.congr_of_eventuallyEq hevent.symm).unique hright
  have : (0 : E →L[ℝ] ℝ) = ell := by
    apply add_left_cancel (a := Dw 0)
    simpa using hlin
  exact this.symm

/-- The affine conclusion on a ball, with the two derivative fields
explicit.  No continuity of the second derivative is required. -/
theorem euler_rigidity_of_hasFDerivAt {w : E → ℝ}
    {Dw : E → E →L[ℝ] ℝ} {DDw : E → E →L[ℝ] (E →L[ℝ] ℝ)}
    {ell : E →L[ℝ] ℝ} {k R : ℝ} (hR : 0 < R)
    (hw : ∀ x ∈ Metric.ball 0 R, HasFDerivAt w (Dw x) x)
    (hDw : ∀ x ∈ Metric.ball 0 R, HasFDerivAt Dw (DDw x) x)
    (heuler : ∀ x ∈ Metric.ball 0 R, Dw x x = w x + ell x + k) :
    ell = 0 ∧ k = -w 0 ∧ ∀ x ∈ Metric.ball 0 R, w x = w 0 + Dw 0 x := by
  have hzero : (0 : E) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  refine ⟨euler_linear_forcing_eq_zero hR (hw 0 hzero) (hDw 0 hzero) heuler, ?_, ?_⟩
  · have h := heuler 0 hzero
    simp only [map_zero, add_zero] at h
    linarith
  · intro x hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
    have hxR : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hradius : 1 < R / ‖x‖ := (lt_div_iff₀ hxnorm).mpr (by simpa using hxR)
    have hray : ∀ t ∈ Ioo (-(R / ‖x‖)) (R / ‖x‖), t • x ∈ Metric.ball 0 R := by
      intro t ht
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
      have h := mul_lt_mul_of_pos_right (abs_lt.mpr ht) hxnorm
      simpa [div_mul_cancel₀ R (ne_of_gt hxnorm)] using h
    have hline (t : ℝ) : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have hfirst : ∀ t ∈ Ioo (-(R / ‖x‖)) (R / ‖x‖),
        HasDerivAt (fun t : ℝ => w (t • x)) (Dw (t • x) x) t := by
      intro t ht
      exact (hw (t • x) (hray t ht)).comp_hasDerivAt t (hline t)
    have hsecond : ∀ t ∈ Ioo (-(R / ‖x‖)) (R / ‖x‖),
        HasDerivAt (fun t : ℝ => Dw (t • x) x) (DDw (t • x) x x) t := by
      intro t ht
      have hD : HasDerivAt (fun s : ℝ => Dw (s • x)) (DDw (t • x) x) t :=
        (hDw (t • x) (hray t ht)).comp_hasDerivAt t (hline t)
      have hc : HasDerivAt (fun _ : ℝ => x) (0 : E) t := hasDerivAt_const t x
      have h := hD.clm_apply hc
      simpa only [map_zero, add_zero] using h
    have hrule : ∀ t ∈ Ioo (-(R / ‖x‖)) (R / ‖x‖),
        t * Dw (t • x) x = w (t • x) + ell x * t + k := by
      intro t ht
      simpa [map_smul, smul_eq_mul, mul_comm] using heuler (t • x) (hray t ht)
    have h := (scalar_euler_ray_affine hradius hfirst hsecond hrule).2.2
    simpa using h

/-- `C²` version of the Euler rigidity theorem used for the smooth
Euclidean limit in `pi:limiting-euler-equation`. -/
theorem euler_rigidity_of_contDiffOn {w : E → ℝ} {ell : E →L[ℝ] ℝ} {k R : ℝ}
    (hR : 0 < R) (hw : ContDiffOn ℝ 2 w (Metric.ball 0 R))
    (heuler : ∀ x ∈ Metric.ball 0 R,
      fderiv ℝ w x x = w x + ell x + k) :
    ell = 0 ∧ k = -w 0 ∧
      ∀ x ∈ Metric.ball 0 R, w x = w 0 + fderiv ℝ w 0 x := by
  apply euler_rigidity_of_hasFDerivAt (DDw := fderiv ℝ (fderiv ℝ w)) hR _ _ heuler
  · intro x hx
    exact ((hw.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt
      (by norm_num)).hasFDerivAt
  · intro x hx
    have hderiv : ContDiffOn ℝ 1 (fderiv ℝ w) (Metric.ball 0 R) :=
      hw.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    exact ((hderiv.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt
      (by norm_num)).hasFDerivAt

end RegularPointCoordinates

end OAI
