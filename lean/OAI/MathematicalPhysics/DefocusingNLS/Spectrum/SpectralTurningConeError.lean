import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningNegativeErrorLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningActionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterNegative

namespace OAI

/-! The error threshold for the forbidden WKB cone follows from the actual
residual integral and action, with the fixed cutoff chosen first. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_eventual_cone_error
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1) :
    ∀ᶠ M : ℝ in atTop, 32 ≤ M ∧ ∀ᶠ n in atTop,
      let J := ∫ t in R..(r₀ n-M*d n), (25/4 : ℝ)*
        ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
          ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖
      let H := (∫ t in R..(r₀ n-M*d n),
        spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ 1/64 := by
  let A : ℝ := 25/4
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  have hj := spectralTurningCutoffError_tendsto.const_mul A
  have hbase : Tendsto (fun M => A*Real.exp (A*spectralTurningCutoffError M)*
      (A*spectralTurningCutoffError M)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,Real.exp_zero,mul_one,mul_assoc] using
      (((Real.continuous_exp.tendsto (A*0)).comp hj).mul hj).const_mul A
  filter_upwards [eventually_ge_atTop (32 : ℝ),
    hbase.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/64))] with M hM hbaseM
  refine ⟨hM,?_⟩
  have hMp : 0 < M := by linarith
  let Jb := fun n => A*spectralTurningNegativeError M R (r₀ n) (d n)
  let H := fun n => (∫ t in R..(r₀ n-M*d n),
    spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t).re
  have hJb : Tendsto Jb atTop (𝓝 (A*spectralTurningCutoffError M)) :=
    (spectralTurningNegativeError_tendsto M R r₀ d hr₀ hd).const_mul A
  have hH : Tendsto H atTop atTop :=
    spectralTurning_forbidden_action_tendsto h b eta omega gamma r₀ d R M hR hMp hr₀ hdata
  have he : Tendsto (fun n => Real.exp (-2*H n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hH.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have htotal : Tendsto (fun n => A*Real.exp (Jb n)*Jb n+(25/8)*Real.exp (-2*H n)) atTop
      (𝓝 (A*Real.exp (A*spectralTurningCutoffError M)*(A*spectralTurningCutoffError M))) := by
    simpa only [Function.comp_def,mul_zero,add_zero,mul_assoc] using
      ((((Real.continuous_exp.tendsto _).comp hJb).mul hJb).const_mul A).add
        (he.const_mul (25/8 : ℝ))
  filter_upwards [hdata,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hr₀.eventually (eventually_ge_atTop (max (2*R) (2*M))),
    htotal.eventually (gt_mem_nhds hbaseM)] with n hn hdn hrn htn
  rcases hn with ⟨hrp,hdn0,heta,hz,hsc⟩
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hdn0
    intro he
    rw [← he] at hsc
    norm_num at hsc
  have hRhalf : R ≤ r₀ n/2 := by linarith [le_trans (le_max_left (2*R) (2*M)) hrn]
  have hMd : M*d n ≤ r₀ n/2 := by nlinarith [le_trans (le_max_right (2*R) (2*M)) hrn]
  let J := ∫ t in R..(r₀ n-M*d n), A*
    ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
      ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg (by linarith)
    (fun t _ => by dsimp only [A]; positivity)
  have hJeq : J = A*(∫ t in R..(r₀ n-M*d n),
      ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
        ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hJle : J ≤ Jb n := by
    rw [hJeq]
    exact mul_le_mul_of_nonneg_left
      (spectralTurning_outer_negative_error h (b n) (eta n) (omega n) (gamma n)
        (r₀ n) (d n) M R heta hrp hdp hMp hR hRhalf hMd hz hsc) (by norm_num)
  change A*Real.exp J*J+(25/8)*Real.exp (-2*H n) ≤ 1/64
  apply le_trans _ htn.le
  gcongr

theorem spectralTurning_eventual_relative_error
    (eps : ℝ) (heps : 0 < eps) (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1) :
    ∀ᶠ M : ℝ in atTop, 32 ≤ M ∧ ∀ᶠ n in atTop,
      let J := ∫ t in R..(r₀ n-M*d n), (25/4 : ℝ)*
        ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
          ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖
      let H := (∫ t in R..(r₀ n-M*d n),
        spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ eps := by
  let A : ℝ := 25/4
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  have hj := spectralTurningCutoffError_tendsto.const_mul A
  have hbase : Tendsto (fun M => A*Real.exp (A*spectralTurningCutoffError M)*
      (A*spectralTurningCutoffError M)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,Real.exp_zero,mul_one,mul_assoc] using
      (((Real.continuous_exp.tendsto (A*0)).comp hj).mul hj).const_mul A
  filter_upwards [eventually_ge_atTop (32 : ℝ),
    hbase.eventually (gt_mem_nhds heps)] with M hM hbaseM
  refine ⟨hM,?_⟩
  have hMp : 0 < M := by linarith
  let Jb := fun n => A*spectralTurningNegativeError M R (r₀ n) (d n)
  let H := fun n => (∫ t in R..(r₀ n-M*d n),
    spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t).re
  have hJb : Tendsto Jb atTop (𝓝 (A*spectralTurningCutoffError M)) :=
    (spectralTurningNegativeError_tendsto M R r₀ d hr₀ hd).const_mul A
  have hH : Tendsto H atTop atTop :=
    spectralTurning_forbidden_action_tendsto h b eta omega gamma r₀ d R M hR hMp hr₀ hdata
  have he : Tendsto (fun n => Real.exp (-2*H n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hH.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have htotal : Tendsto (fun n => A*Real.exp (Jb n)*Jb n+(25/8)*Real.exp (-2*H n)) atTop
      (𝓝 (A*Real.exp (A*spectralTurningCutoffError M)*(A*spectralTurningCutoffError M))) := by
    simpa only [Function.comp_def,mul_zero,add_zero,mul_assoc] using
      ((((Real.continuous_exp.tendsto _).comp hJb).mul hJb).const_mul A).add
        (he.const_mul (25/8 : ℝ))
  filter_upwards [hdata,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hr₀.eventually (eventually_ge_atTop (max (2*R) (2*M))),
    htotal.eventually (gt_mem_nhds hbaseM)] with n hn hdn hrn htn
  rcases hn with ⟨hrp,hdn0,heta,hz,hsc⟩
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hdn0
    intro he
    rw [← he] at hsc
    norm_num at hsc
  have hRhalf : R ≤ r₀ n/2 := by linarith [le_trans (le_max_left (2*R) (2*M)) hrn]
  have hMd : M*d n ≤ r₀ n/2 := by nlinarith [le_trans (le_max_right (2*R) (2*M)) hrn]
  let J := ∫ t in R..(r₀ n-M*d n), A*
    ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
      ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg (by linarith)
    (fun t _ => by dsimp only [A]; positivity)
  have hJeq : J = A*(∫ t in R..(r₀ n-M*d n),
      ‖spectralLiouvilleResidual (-1) h (b n) (eta n) (omega n) (gamma n) t‖/
        ‖spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hJle : J ≤ Jb n := by
    rw [hJeq]
    exact mul_le_mul_of_nonneg_left
      (spectralTurning_outer_negative_error h (b n) (eta n) (omega n) (gamma n)
        (r₀ n) (d n) M R heta hrp hdp hMp hR hRhalf hMd hz hsc) (by norm_num)
  change A*Real.exp J*J+(25/8)*Real.exp (-2*H n) ≤ eps
  apply le_trans _ htn.le
  gcongr

end DefocusingNLS

end OAI
