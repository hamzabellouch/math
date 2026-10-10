import OAI.NumberTheory.CubicMoment.Estimates.MellinSeries

namespace OAI

/-! Absolute Mellin interchange for a smooth sum of positive dilates.
This is used with the actual cube-product norms in the completed series. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma integral_norm_mellin_scale (W : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1)*W (a*x)‖) =
      a^(-s.re)*(∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1)*W x‖) := by
  have he (x : ℝ) (hx : x ∈ Ioi 0) :
      ‖(x:ℂ)^(s-1)*W (a*x)‖ =
        a^(1-s.re)*‖((a*x:ℝ):ℂ)^(s-1)*W (a*x)‖ := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hx)]
    simp only [Complex.sub_re,Complex.one_re]
    rw [Real.mul_rpow ha.le hx.le,←mul_assoc,←mul_assoc,←Real.rpow_add ha]
    have he : 1-s.re+(s.re-1) = 0 := by ring
    rw [he,Real.rpow_zero,one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,
    integral_comp_mul_left_Ioi (fun x : ℝ => ‖(x:ℂ)^(s-1)*W x‖) 0 ha,mul_zero]
  simp only [smul_eq_mul]
  rw [←mul_assoc,←Real.rpow_neg_one a,←Real.rpow_add ha]
  congr 2
  ring

theorem mellin_smooth_scale_series {ι : Type*} [Countable ι]
    (A : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hc : Continuous W) (s : ℂ)
    (hA : Summable (fun i => ‖A i‖*(N i)^(-s.re))) :
    mellin (fun x => ∑' i, A i*W (N i*x)) s =
      mellin W s*normDirichletSeries A N s := by
  let f (i : ι) (x : ℝ) := (x:ℂ)^(s-1)*(A i*W (N i*x))
  have hi (i : ι) : Integrable (f i) (volume.restrict (Ioi 0)) := by
    have h := ((MellinConvergent.comp_mul_left (hN i)).mpr
      (smooth_mellin_convergent W hW hpos hc s)).const_smul (A i)
    simpa only [MellinConvergent,IntegrableOn,smul_eq_mul,f] using h
  have hn (i : ι) : (∫ x : ℝ in Ioi 0, ‖f i x‖) =
      (‖A i‖*(N i)^(-s.re))*(∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1)*W x‖) := by
    have hp (x : ℝ) : ‖f i x‖ = ‖A i‖*‖(x:ℂ)^(s-1)*W (N i*x)‖ := by
      simp only [f,norm_mul]
      ring
    simp_rw [hp]
    rw [integral_const_mul,integral_norm_mellin_scale W s (hN i),mul_assoc]
  have hs : Summable (fun i => ∫ x : ℝ in Ioi 0, ‖f i x‖) := by
    simpa only [hn] using hA.mul_right (∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1)*W x‖)
  calc
    _ = ∫ x : ℝ in Ioi 0, ∑' i, f i x := by simp only [mellin,f,smul_eq_mul,tsum_mul_left]
    _ = ∑' i, ∫ x : ℝ in Ioi 0, f i x := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑' i, A i*((N i:ℂ)^(-s)*mellin W s) := by
      apply tsum_congr
      intro i
      have hf : (fun x => f i x) =
          (fun x : ℝ => A i*((x:ℂ)^(s-1)*W (N i*x))) := by funext x; dsimp [f]; ring
      rw [hf,integral_const_mul]
      exact congrArg (fun z => A i*z) (mellin_comp_mul_left W s (hN i))
    _ = _ := by
      simp only [normDirichletSeries,←tsum_mul_left]
      apply tsum_congr
      intro i
      ring

end CubicFirstMoment

end

end OAI
