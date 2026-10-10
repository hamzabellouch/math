import OAI.MeasureTheory.Falconer.Estimates.LinearNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap

theorem plane_schwartz_fourier_weighted (φ : 𝓢(Plane,ℂ)) (n : ℕ)
    (ξ : Plane) (hξ : ξ ≠ 0) :
    (2*Real.pi)^n*‖ξ‖^n*‖𝓕 (φ : Plane → ℂ) ξ‖ ≤
      ∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖ := by
  have hi (j : ℕ) : Integrable (iteratedFDeriv ℝ j (φ : Plane → ℂ)) := by
    apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 j).mono'
      ((φ.smooth ⊤).continuous_iteratedFDeriv (m := j)
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).aestronglyMeasurable
    filter_upwards with x
    simp
  have he := congrFun (Real.fourier_iteratedFDeriv (N := (⊤:ℕ∞))
    (φ.smooth ⊤) (fun j _ => hi j) (n := n) (by simp)) ξ
  have hb : ‖𝓕 (iteratedFDeriv ℝ n (φ : Plane → ℂ)) ξ‖ ≤
      ∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖ := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ Plane) (iteratedFDeriv ℝ n (φ : Plane → ℂ)) ξ
  let L := VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 (φ : Plane → ℂ)) ξ n
  have hl : ‖L‖ ≤ ∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖ := by
    simpa only [he] using hb
  have hv := (L.le_opNorm (fun _ => ξ)).trans
    (mul_le_mul_of_nonneg_right hl (by positivity))
  have hinner : innerSL ℝ ξ ξ = ‖ξ‖^2 := real_inner_self_eq_norm_sq ξ
  have hv' : ((2*Real.pi)^n*‖ξ‖^n*‖𝓕 (φ : Plane → ℂ) ξ‖)*‖ξ‖^n ≤
      (∫ x : Plane, ‖iteratedFDeriv ℝ n (φ : Plane → ℂ) x‖)*‖ξ‖^n := by
    simpa [L,VectorFourier.fourierPowSMulRight_apply, norm_smul,
      hinner,Finset.prod_const,
      abs_pow,abs_norm,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      pow_two,mul_pow,mul_assoc,mul_left_comm,mul_comm] using hv
  exact (mul_le_mul_iff_left₀ (pow_pos (norm_pos_iff.mpr hξ) n)).mp hv'

theorem plane_compact_fourier_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Metric.closedBall (0:Plane) 8) (n : ℕ) {C D : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*D^n) (ξ : Plane) (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ (C*D^n*volume.real (Metric.closedBall (0:Plane) 8))/
      ((2*Real.pi)^n*‖ξ‖^n) := by
  have hc : HasCompactSupport f :=
    (isCompact_closedBall (0:Plane) 8).of_isClosed_subset isClosed_closure hs
  let φ := hc.toSchwartzMap hf
  have hw := plane_schwartz_fourier_weighted φ n ξ hξ
  change (2*Real.pi)^n*‖ξ‖^n*‖𝓕 f ξ‖ ≤ ∫ x, ‖iteratedFDeriv ℝ n f x‖ at hw
  have hz (x : Plane) (hx : x ∉ Metric.closedBall (0:Plane) 8) :
      ‖iteratedFDeriv ℝ n f x‖ = 0 := by
    apply norm_eq_zero.mpr
    apply Function.notMem_support.mp
    intro hm
    exact hx (hs (support_iteratedFDeriv_subset n hm))
  have he := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : Plane => ‖iteratedFDeriv ℝ n f x‖)
    (s := Metric.closedBall (0:Plane) 8) (C := C*D^n)
    (isCompact_closedBall (0:Plane) 8).measure_lt_top
    (Filter.Eventually.of_forall (fun x => by simpa using hb x))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at he
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n*‖ξ‖^n)).mpr
    (by simpa only [mul_comm (‖𝓕 f ξ‖)] using hw.trans he)

end PlanarFalconer

end OAI
