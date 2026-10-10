import OAI.Probability.SLE.Geometry.TransverseCurveDifference
import OAI.Probability.SLE.Loewner.UnivalentInverseAnalytic
import OAI.Probability.SLE.DyadicStrips

namespace OAI

/-! Radial and angular image curves cross transversely under an actual
univalent half-plane map. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_polar_point_mem (x r θ : ℝ) (hr : 0<r) (hθ : θ∈Ioo 0 Real.pi) :
    (x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)∈upperHalfPlane := by
  have he := exp_strip_halfplane (x := (θ:ℂ)*Complex.I) (by simpa using hθ)
  change 0<((x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im
  simpa only [Set.mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,zero_mul,add_zero,zero_add] using mul_pos hr he

lemma holomorphic_polar_arc_strict {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (x r θ : ℝ) (hr : 0<r)
    (hθ : θ∈Ioo 0 Real.pi) :
    HasStrictDerivAt (fun u : ℝ => F ((x:ℂ)+(r:ℂ)*Complex.exp ((u:ℂ)*Complex.I)))
      (deriv F ((x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) *
        ((r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*Complex.I)) θ := by
  have hd := (hF.analyticAt (isOpen_upperHalfPlane.mem_nhds
    (univalent_polar_point_mem x r θ hr hθ))).hasStrictDerivAt
  have hi : HasStrictDerivAt (fun u : ℝ => (u:ℂ)*Complex.I) Complex.I θ := by
    simpa using (Complex.ofRealCLM.hasStrictDerivAt (x := θ)).mul_const Complex.I
  have he := ((Complex.hasStrictDerivAt_exp ((θ:ℂ)*Complex.I)).hasStrictFDerivAt.restrictScalars ℝ).comp_hasStrictDerivAt θ hi
  have ha := (he.const_mul (r:ℂ)).const_add (x:ℂ)
  have hf := (hd.hasStrictFDerivAt.restrictScalars ℝ).comp_hasStrictDerivAt θ ha
  simpa [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm,
    Function.comp_def] using hf

lemma holomorphic_polar_ray_strict {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (x r θ : ℝ) (hr : 0<r)
    (hθ : θ∈Ioo 0 Real.pi) :
    HasStrictDerivAt (fun u : ℝ => F ((x:ℂ)+(u:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))
      (deriv F ((x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) *
        Complex.exp ((θ:ℂ)*Complex.I)) r := by
  have hd := (hF.analyticAt (isOpen_upperHalfPlane.mem_nhds
    (univalent_polar_point_mem x r θ hr hθ))).hasStrictDerivAt
  have ha : HasStrictDerivAt
      (fun u : ℝ => (x:ℂ)+(u:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (Complex.exp ((θ:ℂ)*Complex.I)) r := by
    simpa using ((Complex.ofRealCLM.hasStrictDerivAt (x := r)).mul_const
      (Complex.exp ((θ:ℂ)*Complex.I))).const_add (x:ℂ)
  have hf := (hd.hasStrictFDerivAt.restrictScalars ℝ).comp_hasStrictDerivAt r ha
  simpa [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,mul_comm,Function.comp_def] using hf

lemma univalent_arc_ray_locally_injective {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hi : InjOn F upperHalfPlane)
    (x r θ : ℝ) (hr : 0<r) (hθ : θ∈Ioo 0 Real.pi) :
    ∃ δ : ℝ, 0<δ ∧ InjOn (fun z : ℂ =>
      F ((x:ℂ)+(r:ℂ)*Complex.exp ((z.im:ℂ)*Complex.I))-
      F ((x:ℂ)+(z.re:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))
      (closedBall ((r:ℂ)+(θ:ℂ)*Complex.I) δ) := by
  apply transverse_difference_locally_injective
    (holomorphic_polar_arc_strict hF x r θ hr hθ)
    (holomorphic_polar_ray_strict hF x r θ hr hθ)
  let q := deriv F ((x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))*Complex.exp ((θ:ℂ)*Complex.I)
  have hq : q≠0 := mul_ne_zero
    (univalent_deriv_ne_zero isOpen_upperHalfPlane hF hi (univalent_polar_point_mem x r θ hr hθ))
    (Complex.exp_ne_zero _)
  have hα : deriv F ((x:ℂ)+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) *
      ((r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*Complex.I)=(r:ℂ)*Complex.I*q := by
    dsimp [q]
    ring
  rw [hα]
  simpa only [Complex.ofReal_one,one_mul] using
    transverse_radial_angular r 1 q hr.ne' one_ne_zero hq

end SLEExactGauge

end

end OAI
