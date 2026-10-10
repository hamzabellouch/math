import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialHeight

namespace OAI

/-! The actual reflected-height tail estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicTheta_radial_remainder_negative_tail_mean {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-A))
    (htail : ∀ t : ℝ, |t|≤2*T →
      ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
    (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r W X (-t)‖)/T≤
      81*((∫ t in T..2*T,‖metaplecticPrefactor r 0*
        ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase (-t) x) A (X/729) nd‖)/T+
        ‖metaplecticPrefactor r 0‖*E) := by
  let F := fun t : ℝ => cubicThetaRadialHeightRemainder r W X (-t)
  let P := fun t : ℝ => metaplecticPrefactor r 0*
    ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase (-t) x) A (X/729) nd
  have hF : Continuous F := (continuous_cubicThetaRadialHeightRemainder hr W hW hpos hsm hX).comp continuous_id.neg
  have hP : Continuous P := continuous_const.mul
    ((continuous_metaplectic_retained cubicThetaCoreCoefficient hr 0 W hW hpos hsm hA.le
      (div_pos hX (by norm_num : (0:ℝ)<729)) J hm hp).comp continuous_id.neg)
  have hb (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖F t‖≤81*‖P t‖+81*‖metaplecticPrefactor r 0‖*E := by
    have habs : |-t|≤2*T := by rw [abs_neg,abs_of_nonneg (hT.le.trans ht.1)]; exact ht.2
    obtain ⟨hS,hE⟩ := cubicTheta_radial_height_voronoi hr hsr W hW hpos hsm hX hA (-t)
    rw [metaplecticDualTerm_split cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase (-t) x) A (X/729) J hS] at hE
    have he : F t=mellinPhase (-t) X*(81*(P t+metaplecticPrefactor r 0*
        ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase (-t) x) A (X/729) J nd)) := by
      dsimp only [F,P]
      rw [hE]
      ring
    rw [he,norm_mul,mellinPhase_norm,one_mul,norm_mul,Complex.norm_ofNat]
    have hadd := norm_add_le (P t) (metaplecticPrefactor r 0*
      ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase (-t) x) A (X/729) J nd)
    have hbound := mul_le_mul_of_nonneg_left (htail (-t) habs)
      (_root_.norm_nonneg (metaplecticPrefactor r 0))
    have htailnorm : ‖metaplecticPrefactor r 0*
        ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase (-t) x) A (X/729) J nd‖≤‖metaplecticPrefactor r 0‖*E := by
      rw [norm_mul]
      exact hbound
    have hh := hadd.trans (add_le_add le_rfl htailnorm)
    nlinarith only [hh]
  have hFi : IntervalIntegrable (fun t => ‖F t‖) volume T (2*T) :=
    hF.norm.intervalIntegrable T (2*T)
  have hPi : IntervalIntegrable (fun t => (81:ℝ)*‖P t‖) volume T (2*T) :=
    (continuous_const.mul hP.norm).intervalIntegrable T (2*T)
  have hCi : IntervalIntegrable (fun _ : ℝ => 81*‖metaplecticPrefactor r 0‖*E) volume T (2*T) :=
    continuous_const.intervalIntegrable T (2*T)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (show T≤2*T by linarith)
    hFi (hPi.add hCi) hb
  apply (div_le_iff₀ hT).mpr
  apply hi.trans_eq
  rw [intervalIntegral.integral_add hPi hCi,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  dsimp only [F,P]
  field_simp [hT.ne']
  ring

end CubicFirstMoment

end

end OAI
