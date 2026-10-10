import OAI.Probability.SLE.Geometry.SmallImageSemicircle

namespace OAI

/-! Complex-valued angular sections have small diameter when their
one-dimensional derivative energy is small. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma complex_angular_oscillation {f : ℝ → ℂ} {x y : ℝ}
    (hx : x∈Ioo 0 Real.pi) (hy : y∈Ioo 0 Real.pi)
    (hf : ∀ θ∈uIcc x y, DifferentiableAt ℝ f θ)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioo 0 Real.pi))) :
    ‖f y-f x‖ ≤ Real.sqrt Real.pi *
      Real.sqrt (∫ θ in Ioo 0 Real.pi, ‖deriv f θ‖^2) := by
  have hsub : uIoc x y⊆Ioo 0 Real.pi := by
    intro θ hθ
    exact ordConnected_Ioo.uIcc_subset hx hy (uIoc_subset_uIcc hθ)
  have hi : IntegrableOn (fun θ => ‖deriv f θ‖) (Ioo 0 Real.pi) :=
    (hd.integrable (by norm_num)).norm
  have hi' : IntegrableOn (deriv f) (Ioo 0 Real.pi) := hd.integrable (by norm_num)
  have hid : IntervalIntegrable (deriv f) volume x y :=
    intervalIntegrable_iff.mpr (hi'.mono_set hsub)
  calc
    ‖f y-f x‖ = ‖∫ θ in x..y, deriv f θ‖ :=
      congrArg norm (intervalIntegral.integral_deriv_eq_sub hf hid).symm
    _ ≤ ∫ θ in uIoc x y, ‖deriv f θ‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ θ in Ioo 0 Real.pi, ‖deriv f θ‖ :=
      setIntegral_mono_set hi (ae_of_all _ (fun _ => norm_nonneg _)) hsub.eventuallySubset
    _ ≤ _ := by
      simpa only [abs_norm] using SmallImageSemicircle.integral_abs_le_angular_energy hd.norm

lemma holomorphic_angular_section_absolutelyContinuous
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | 0<z.im ∧ z.im<Real.pi})
    (v : ℝ) {x y : ℝ} (hx : x∈Ioo 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    AbsolutelyContinuousOnInterval (fun θ : ℝ => f ((v:ℂ)+(θ:ℂ)*Complex.I)) x y := by
  have hc : ContDiffOn ℝ 1 (fun θ : ℝ => f ((v:ℂ)+(θ:ℂ)*Complex.I)) (uIcc x y) := by
    intro θ hθ
    have hθ' := ordConnected_Ioo.uIcc_subset hx hy hθ
    have hz : (v:ℂ)+(θ:ℂ)*Complex.I∈{z : ℂ | 0<z.im ∧ z.im<Real.pi} := by
      simpa only [Set.mem_Ioo,Set.mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hθ'
    have ho : IsOpen {z : ℂ | 0<z.im ∧ z.im<Real.pi} :=
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have ha : ContDiffAt ℝ 1 f ((v:ℂ)+(θ:ℂ)*Complex.I) :=
      ((hf.analyticAt (ho.mem_nhds hz)).restrictScalars (𝕜 := ℝ)).contDiffAt
    have hcast : ContDiffAt ℝ 1 (fun t : ℝ => (t:ℂ)) θ :=
      Complex.ofRealCLM.contDiff.contDiffAt
    exact (ha.comp θ (contDiffAt_const.add (hcast.mul contDiffAt_const))).contDiffWithinAt
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_uIcc x y) isCompact_uIcc
  exact hK.absolutelyContinuousOnInterval

end SLEExactGauge

end

end OAI
