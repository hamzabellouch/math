import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularWeighted

namespace OAI

/-! The weighted regular-origin integral is a bounded complex-linear map. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralRegularWeightedSource (α : ℝ) (f : ℝ →ᵇ ℂ) (s : ℝ) : ℂ :=
  (Real.exp (α*s^2) : ℂ)*f s

theorem spectralRegularWeightedSource_continuous (α : ℝ) (f : ℝ →ᵇ ℂ) :
    Continuous (spectralRegularWeightedSource α f) := by
  unfold spectralRegularWeightedSource
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul f.continuous

theorem spectralRegularWeightedSource_bound (α : ℝ) (f : ℝ →ᵇ ℂ) (s : ℝ) :
    ‖spectralRegularWeightedSource α f s‖ ≤ ‖f‖*Real.exp (α*s^2) := by
  rw [spectralRegularWeightedSource,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_comm]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm s) (Real.exp_pos _).le

noncomputable def spectralRegularWeightedValue (d : ℕ) (h R α : ℝ)
    (f : ℝ →ᵇ ℂ) (r : ℝ) : ℂ :=
  (Real.exp (-α*(radialClamp R r)^2) : ℂ)*
    spectralRegularPrimitive d h (spectralRegularWeightedSource α f) (radialClamp R r)

theorem spectralRegularWeightedValue_continuous (d : ℕ) (h R α : ℝ) (f : ℝ →ᵇ ℂ) :
    Continuous (spectralRegularWeightedValue d h R α f) := by
  unfold spectralRegularWeightedValue
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_radialClamp R).pow 2)))
  · exact (spectralRegularPrimitive_continuous d h _
      (spectralRegularWeightedSource_continuous α f)).comp (continuous_radialClamp R)

theorem spectralRegularWeightedValue_bound (d : ℕ) (h R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (f : ℝ →ᵇ ℂ) (r : ℝ) :
    ‖spectralRegularWeightedValue d h R α f r‖ ≤ ‖f‖/(2*α) := by
  let x := radialClamp R r
  have hb := spectralRegularPrimitive_weighted_bound d h R α ‖f‖ x hα
    (norm_nonneg _) (radialClamp_mem R r hR) (spectralRegularWeightedSource α f)
    (fun s _ => spectralRegularWeightedSource_bound α f s)
  change ‖(Real.exp (-α*x^2) : ℂ)*spectralRegularPrimitive d h _ x‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-α*x^2)*Real.exp (α*x^2)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  calc
    _ ≤ Real.exp (-α*x^2)*(‖f‖*Real.exp (α*x^2)/(2*α)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (Real.exp (-α*x^2)*Real.exp (α*x^2))*‖f‖/(2*α) := by ring
    _ = _ := by rw [he,one_mul]

noncomputable def spectralRegularWeightedKernel (d : ℕ) (h R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (f : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (spectralRegularWeightedValue d h R α f)
    (spectralRegularWeightedValue_continuous d h R α f) (‖f‖/(2*α))
    (spectralRegularWeightedValue_bound d h R α hR hα f)

theorem spectralRegularWeightedKernel_norm (d : ℕ) (h R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (f : ℝ →ᵇ ℂ) :
    ‖spectralRegularWeightedKernel d h R α hR hα f‖ ≤ ‖f‖/(2*α) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  exact spectralRegularWeightedValue_bound d h R α hR hα f

noncomputable def spectralRegularKernelCLM (d : ℕ) (h R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) : (ℝ →ᵇ ℂ) →L[ℂ] (ℝ →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := spectralRegularWeightedKernel d h R α hR hα
      map_add' := by
        intro f g
        apply BoundedContinuousFunction.ext
        intro r
        change spectralRegularWeightedValue d h R α (f+g) r=
          spectralRegularWeightedValue d h R α f r+spectralRegularWeightedValue d h R α g r
        have hs : spectralRegularWeightedSource α (f+g)=
            fun s => spectralRegularWeightedSource α f s+spectralRegularWeightedSource α g s := by
          funext s
          simp only [spectralRegularWeightedSource,BoundedContinuousFunction.add_apply,mul_add]
        unfold spectralRegularWeightedValue
        rw [hs,spectralRegularPrimitive_add d h _ _
          (spectralRegularWeightedSource_continuous α f)
          (spectralRegularWeightedSource_continuous α g),mul_add]
      map_smul' := by
        intro c f
        apply BoundedContinuousFunction.ext
        intro r
        change spectralRegularWeightedValue d h R α (c • f) r=
          c*spectralRegularWeightedValue d h R α f r
        have hs : spectralRegularWeightedSource α (c • f)=
            fun s => c*spectralRegularWeightedSource α f s := by
          funext s
          simp only [spectralRegularWeightedSource,BoundedContinuousFunction.smul_apply,
            smul_eq_mul]
          ring
        unfold spectralRegularWeightedValue
        rw [hs,spectralRegularPrimitive_smul]
        ring }
    (1/(2*α)) (fun f => by
      change ‖spectralRegularWeightedKernel d h R α hR hα f‖ ≤ (1/(2*α))*‖f‖
      rw [one_div_mul_eq_div]
      exact spectralRegularWeightedKernel_norm d h R α hR hα f)

theorem spectralRegularKernelCLM_norm (d : ℕ) (h R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) :
    ‖spectralRegularKernelCLM d h R α hR hα‖ ≤ 1/(2*α) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end DefocusingNLS

end OAI
