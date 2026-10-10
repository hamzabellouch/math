import Mathlib
import OAI.Analysis.Crouzeix.HarmonicReflection

namespace OAI

/-! Reflection Derivative. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem circleAverage_neg {R : ℝ} (hR : 0 < R) {v : ℂ → ℝ}
    (hv : ContinuousOn v (sphere 0 R)) (hle : ∀ z ∈ sphere 0 R, v z ≤ 0)
    (hlt : v ((R : ℂ) * I) < 0) : circleAverage v 0 R < 0 := by
  have hmap : MapsTo (circleMap 0 R) (Icc 0 (2 * π)) (sphere 0 R) :=
    fun t _ => by simpa only [abs_of_pos hR] using circleMap_mem_sphere' 0 R t
  have hc : ContinuousOn (fun t => v (circleMap 0 R t)) (Icc 0 (2 * π)) :=
    hv.comp (continuous_circleMap 0 R).continuousOn hmap
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0 : ℝ) < 2 * π by positivity) hc continuousOn_const
    (fun t ht => hle _ (hmap (Ioc_subset_Icc_self ht))) (show ∃ t ∈ Icc 0 (2 * π), v (circleMap 0 R t) < 0 from
      ⟨π / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, by
        simpa only [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
          Real.sin_pi_div_two, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_add]
          using hlt⟩)
  simp only [intervalIntegral.integral_zero] at hi
  simpa only [circleAverage, smul_eq_mul] using
    mul_neg_of_pos_of_neg (inv_pos.mpr (by positivity : 0 < 2 * π)) hi

theorem im_deriv_schwarzExtension_zero {R : ℝ} (hR : 0 < R) {v : ℂ → ℝ}
    (hv : ContinuousOn v (sphere 0 R)) :
    (deriv (schwarzExtension R v) 0).im =
      -2 / R ^ 2 * circleAverage (fun z => z.im * v z) 0 R := by
  have hvi : CircleIntegrable (fun z => (v z : ℂ)) 0 R :=
    ContinuousOn.circleIntegrable hR.le (continuous_ofReal.comp_continuousOn hv)
  have hd := hasDerivAt_circleAverage_herglotzRieszKernel_smul hvi
    (by simpa only [mem_sphere, dist_self, abs_of_pos hR] using hR.ne :
      (0 : ℂ) ∉ sphere 0 |R|)
  have he : deriv (schwarzExtension R v) 0 =
      circleAverage (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ)) 0 R := by
    rw [show schwarzExtension R v =
      (fun w => circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (v ζ : ℂ)) 0 R) by rfl,
      hd.deriv]
    apply circleAverage_congr_sphere
    intro ζ hζ
    have hz : ζ ≠ 0 := by
      intro he
      have hn : ‖ζ‖ = R := by simpa only [abs_of_pos hR] using mem_sphere_zero_iff_norm.mp hζ
      exact hR.ne' (by simpa only [he, norm_zero] using hn.symm)
    simp only [sub_zero, smul_eq_mul]
    congr 1
    field_simp
  have hgi : CircleIntegrable (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    refine (continuousOn_const.div continuousOn_id (fun ζ hζ => ?_)).mul
      (continuous_ofReal.comp_continuousOn hv)
    intro he
    change ζ = 0 at he
    have hn := mem_sphere_zero_iff_norm.mp hζ
    exact hR.ne' (by simpa only [he, norm_zero] using hn.symm)
  rw [he]
  change Complex.imCLM (circleAverage (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ)) 0 R) = _
  rw [← Complex.imCLM.circleAverage_comp_comm hgi]
  have heq : circleAverage (Complex.imCLM ∘ (fun ζ : ℂ => (2 / ζ) * (v ζ : ℂ))) 0 R =
      circleAverage (fun z => (-2 / R ^ 2) • (z.im * v z)) 0 R := by
    apply circleAverage_congr_sphere
    intro z hz
    have hn : ‖z‖ = R := by simpa only [abs_of_pos hR] using mem_sphere_zero_iff_norm.mp hz
    simp only [Function.comp_apply, Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, Complex.div_im, Complex.im_ofNat,
      Complex.re_ofNat, zero_mul, Complex.normSq_eq_norm_sq, hn, smul_eq_mul]
    ring
  rw [heq, circleAverage_fun_smul, smul_eq_mul]

theorem deriv_schwarzExtension_odd_ne_zero {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn (oddReflection u) (sphere 0 R))
    (hneg : ∀ z ∈ sphere (0 : ℂ) R, 0 < z.im → u z < 0) :
    deriv (schwarzExtension R (oddReflection u)) 0 ≠ 0 := by
  have hp : (R : ℂ) * I ∈ sphere (0 : ℂ) R := by
    simp only [mem_sphere_zero_iff_norm, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
  have him : ((R : ℂ) * I).im = R := by simp
  have hle : ∀ z ∈ sphere (0 : ℂ) R, z.im * oddReflection u z ≤ 0 := by
    intro z hz
    rcases lt_trichotomy z.im 0 with hn | he | hp
    · rw [oddReflection, ite_eq_right (not_le.mpr hn)]
      have hconj : conj z ∈ sphere (0 : ℂ) R := by
        simpa only [mem_sphere_zero_iff_norm, Complex.norm_conj] using hz
      have hn' := hneg (conj z) hconj (by simpa only [conj_im] using neg_pos.mpr hn)
      exact mul_nonpos_of_nonpos_of_nonneg hn.le (neg_nonneg.mpr hn'.le)
    · rw [he, zero_mul]
    · rw [oddReflection, ite_eq_left hp.le]
      exact mul_nonpos_of_nonneg_of_nonpos hp.le (hneg z hz hp).le
  have hav := circleAverage_neg hR (Complex.continuous_im.continuousOn.mul hu) hle
    (show ((R : ℂ) * I).im * oddReflection u ((R : ℂ) * I) < 0 by
      rw [him, oddReflection, him, ite_eq_left hR.le]
      exact mul_neg_of_pos_of_neg hR (hneg _ hp (by simpa only [him] using hR)))
  have hpim : 0 < (deriv (schwarzExtension R (oddReflection u)) 0).im := by
    rw [im_deriv_schwarzExtension_zero hR hu]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hR)) hav
  intro he
  simp only [he, zero_im, lt_irrefl] at hpim

end CrouzeixHilbert.Conformal

end

end OAI
