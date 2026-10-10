import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarIntervalBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCentralWeight

namespace OAI

/-! The actual Cauchy equation has a uniform transfer estimate between any
two central points in the same continuous regularized frequency norm. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_regularized_central_transfer
    (h b eta omega gamma r₀ d M : ℝ) (hd : 0 < d) (hM : 0 ≤ M)
    (hcoef : ∀ xi ∈ Icc (-M) M,
      ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖ ≤ M+1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc (r₀-d*M) (r₀+d*M)))
    (hD : ∀ t ∈ Icc (r₀-d*M) (r₀+d*M), HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t)
    (xi zeta : ℝ) (hxi : xi ∈ Icc (-M) M) (hzeta : zeta ∈ Icc (-M) M) (hxz : xi ≤ zeta) :
    let k := spectralTurningRegularizedWeight h b eta omega gamma d
    let C := (M+3+(1 : ℝ)⁻¹)*max (1 : ℝ)⁻¹ (M+3)*Real.exp ((1+(M+1))*(M-(-M)))
    spectralShellNorm (k (r₀+d*zeta)) (q (r₀+d*zeta)) ≤
      C*spectralShellNorm (k (r₀+d*xi)) (q (r₀+d*xi)) ∧
    spectralShellNorm (k (r₀+d*xi)) (q (r₀+d*xi)) ≤
      C*spectralShellNorm (k (r₀+d*zeta)) (q (r₀+d*zeta)) := by
  let s := Real.sqrt d
  let k := spectralTurningRegularizedWeight h b eta omega gamma d
  let K := fun t => s*k (r₀+d*t)
  let Q := spectralTurningState r₀ d s q
  let V := spectralTurningCoefficient h b eta omega gamma r₀ d
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hs2 : s^2 = d := Real.sq_sqrt hd.le
  have hmem (t : ℝ) (ht : t ∈ Icc (-M) M) : r₀+d*t ∈ Icc (r₀-d*M) (r₀+d*M) := by
    constructor <;> nlinarith [ht.1,ht.2]
  have hQc : ContinuousOn Q (Icc (-M) M) :=
    ((hq.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hmem).fst.div_const _).prodMk
      (continuousOn_const.mul (hq.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hmem).snd)
  have hQD (t : ℝ) (ht : t ∈ Icc (-M) M) : HasDerivAt Q (spectralScalarField (V t) (Q t)) t := by
    simpa only [Q,V,spectralTurningCoefficient,Complex.ofReal_pow] using
      spectralTurningState_hasDerivAt r₀ d s t hs.ne' hs2 q _ (hD _ (hmem t ht))
  have hK (t : ℝ) (ht : t ∈ Icc (-M) M) : 1 ≤ K t ∧ K t ≤ M+3 :=
    spectralTurningRegularizedWeight_scaled_bounds h b eta omega gamma r₀ d t M hd hM (hcoef t ht)
  have hb := spectralScalar_interval_shell_subinterval (-M) M (M+1) 1 (M+3)
    (by linarith) (by positivity) (by norm_num) V K Q hQc hQD hcoef hK xi zeta hxi hzeta hxz
  have hnorm (t : ℝ) : spectralShellNorm (K t) (Q t) = spectralShellNorm (k (r₀+d*t)) (q (r₀+d*t)) :=
    spectralTurningState_shell_norm r₀ d s t (k (r₀+d*t)) hs
      (spectralTurningRegularizedWeight_pos h b eta omega gamma d _ hd) q
  simpa only [hnorm] using hb


theorem spectralTurning_regularized_physical_transfer
    (h b eta omega gamma r₀ d M : ℝ) (hd : 0 < d) (hM : 0 ≤ M)
    (hcoef : ∀ xi ∈ Icc (-M) M,
      ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖ ≤ M+1)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc (r₀-d*M) (r₀+d*M)))
    (hD : ∀ t ∈ Icc (r₀-d*M) (r₀+d*M), HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t)
    (r t : ℝ) (hr : r ∈ Icc (r₀-d*M) (r₀+d*M))
    (ht : t ∈ Icc (r₀-d*M) (r₀+d*M)) (hrt : r ≤ t) :
    let k := spectralTurningRegularizedWeight h b eta omega gamma d
    let C := (M+3+(1 : ℝ)⁻¹)*max (1 : ℝ)⁻¹ (M+3)*Real.exp ((1+(M+1))*(M-(-M)))
    spectralShellNorm (k t) (q t) ≤ C*spectralShellNorm (k r) (q r) ∧
    spectralShellNorm (k r) (q r) ≤ C*spectralShellNorm (k t) (q t) := by
  let xi := (r-r₀)/d
  let zeta := (t-r₀)/d
  have hxi : xi ∈ Icc (-M) M := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hr.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [hr.2]
  have hzeta : zeta ∈ Icc (-M) M := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [ht.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [ht.2]
  have hxz : xi ≤ zeta := div_le_div_of_nonneg_right (sub_le_sub_right hrt r₀) hd.le
  have heR : r₀+d*xi = r := by dsimp only [xi]; field_simp; ring
  have heT : r₀+d*zeta = t := by dsimp only [zeta]; field_simp; ring
  simpa only [heR,heT] using spectralTurning_regularized_central_transfer
    h b eta omega gamma r₀ d M hd hM hcoef q hq hD xi zeta hxi hzeta hxz


theorem spectralTurning_regularized_central_family
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G : ℝ) (hM : 0 ≤ M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ q : ℝ → ℂ × ℂ,
      ContinuousOn q (Icc (r₀ n-d n*M) (r₀ n+d n*M)) →
      (∀ t ∈ Icc (r₀ n-d n*M) (r₀ n+d n*M), HasDerivAt q
        (spectralScalarField ((homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) t : ℂ)+
          Complex.I*(gamma n : ℂ)) (q t)) t) →
      ∀ xi ∈ Icc (-M) M, ∀ zeta ∈ Icc (-M) M, xi ≤ zeta →
        let k := spectralTurningRegularizedWeight h (b n) (eta n) (omega n) (gamma n) (d n)
        spectralShellNorm (k (r₀ n+d n*zeta)) (q (r₀ n+d n*zeta)) ≤
          C*spectralShellNorm (k (r₀ n+d n*xi)) (q (r₀ n+d n*xi)) ∧
        spectralShellNorm (k (r₀ n+d n*xi)) (q (r₀ n+d n*xi)) ≤
          C*spectralShellNorm (k (r₀ n+d n*zeta)) (q (r₀ n+d n*zeta)) := by
  let C := (M+3+(1 : ℝ)⁻¹)*max (1 : ℝ)⁻¹ (M+3)*Real.exp ((1+(M+1))*(M-(-M)))
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  have hu := spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d M G hM hr₀ hdata
  filter_upwards [hdata,(Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)] with n hn hc
  have hd : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro he
    have hh := hn.2.2.2.2.2
    rw [← he] at hh
    norm_num at hh
  have hcoef (xi : ℝ) (hxi : xi ∈ Icc (-M) M) :
      ‖spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) xi‖ ≤ M+1 := by
    have he : ‖spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n) xi-
        (xi : ℂ)‖ ≤ 1 := by
      simpa only [dist_eq_norm,norm_sub_rev] using (hc xi hxi).le
    have hx : ‖(xi : ℂ)‖ ≤ M := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hxi
    have hb := norm_add_le (spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n)
      (r₀ n) (d n) xi-(xi : ℂ)) (xi : ℂ)
    rw [sub_add_cancel] at hb
    linarith
  intro q hq hD xi hxi zeta hzeta hxz
  exact spectralTurning_regularized_central_transfer h (b n) (eta n) (omega n) (gamma n)
    (r₀ n) (d n) M hd hM hcoef q hq hD xi zeta hxi hzeta hxz

end DefocusingNLS

end OAI
