import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialPoleBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialLow
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedContinuity

namespace OAI

/-! Exact norm twists and finite dual-tail reduction for the actual radial
remainder. Its main term is the computed one, not an assumed normalization. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaRadialHeightRemainder (r : Eisenstein) (W : ℝ→ℂ) (X t : ℝ) : ℂ :=
  metaplecticHeightCompleted r 0 W X t-mellinPhase t X*
    cubicThetaActualCompletedRadialMain r (fun x => W x*mellinPhase t x) X

lemma continuous_cubicThetaRadialHeightMain {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0<X) :
    Continuous (fun t : ℝ => mellinPhase t X*
      cubicThetaActualCompletedRadialMain r (fun x => W x*mellinPhase t x) X) := by
  have hB : star cubicThetaArithmeticBaseScalar≠0 := star_ne_zero.mpr cubicThetaArithmeticBaseScalar_ne_zero
  have he (t : ℝ) : mellinPhase t X*cubicThetaActualCompletedRadialMain r
      (fun x => W x*mellinPhase t x) X=
      (mellinPhase t X*metaplecticMain r 0 (fun x => W x*mellinPhase t x) X)/
        star cubicThetaArithmeticBaseScalar := by
    apply (eq_div_iff hB).mpr
    rw [mul_assoc,cubicThetaActualCompletedRadialMain_mul_base hr _ hX]
  exact ((continuous_metaplectic_height_main r 0 W hW hpos hsm X).div_const _).congr
    (fun t => (he t).symm)

lemma continuous_cubicThetaRadialHeightRemainder {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0<X) :
    Continuous (cubicThetaRadialHeightRemainder r W X) :=
  (continuous_metaplectic_height_completed r 0 W hW hX).sub
    (continuous_cubicThetaRadialHeightMain hr W hW hpos hsm hX)

theorem cubicTheta_radial_height_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X A : ℝ} (hX : 0<X) (hA : 0<A) (t : ℝ) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase t x) A (X/729)) ∧
    cubicThetaRadialHeightRemainder r W X t=mellinPhase t X*
      (81*metaplecticPrefactor r 0*∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) nd) := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  have htW := phaseWeight_compact hW t
  have htP := phaseWeight_positive hpos t
  have htS := phaseWeight_smooth hpos hsm t
  refine ⟨(cubicTheta_raw_radial_voronoi hr hs _ htW htP htS hA hX).1,?_⟩
  rw [cubicThetaRadialHeightRemainder,metaplecticHeightCompleted_twist r 0 W hX t,
    cubicTheta_completed_radial_voronoi hr hs _ htW htP htS hA hX,mul_add,add_sub_cancel_right]

theorem cubicTheta_radial_remainder_tail_mean {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-A))
    (htail : ∀ t : ℝ, |t|≤2*T →
      ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
    (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r W X t‖)/T≤
      81*((∫ t in T..2*T,‖metaplecticPrefactor r 0*
        ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase t x) A (X/729) nd‖)/T+
        ‖metaplecticPrefactor r 0‖*E) := by
  let F := fun t : ℝ => cubicThetaRadialHeightRemainder r W X t
  let P := fun t : ℝ => metaplecticPrefactor r 0*
    ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase t x) A (X/729) nd
  have hF : Continuous F := continuous_cubicThetaRadialHeightRemainder hr W hW hpos hsm hX
  have hP : Continuous P := continuous_const.mul
    (continuous_metaplectic_retained cubicThetaCoreCoefficient hr 0 W hW hpos hsm hA.le
      (div_pos hX (by norm_num : (0:ℝ)<729)) J hm hp)
  have hb (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖F t‖≤81*‖P t‖+81*‖metaplecticPrefactor r 0‖*E := by
    have habs : |t|≤2*T := by rw [abs_of_nonneg (hT.le.trans ht.1)]; exact ht.2
    obtain ⟨hS,hE⟩ := cubicTheta_radial_height_voronoi hr hsr W hW hpos hsm hX hA t
    rw [metaplecticDualTerm_split cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase t x) A (X/729) J hS] at hE
    have he : F t=mellinPhase t X*(81*(P t+metaplecticPrefactor r 0*
        ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase t x) A (X/729) J nd)) := by
      dsimp only [F,P]
      rw [hE]
      ring
    rw [he,norm_mul,mellinPhase_norm,one_mul,norm_mul,Complex.norm_ofNat]
    have hadd := norm_add_le (P t) (metaplecticPrefactor r 0*
      ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) J nd)
    have hbound := mul_le_mul_of_nonneg_left (htail t habs)
      (_root_.norm_nonneg (metaplecticPrefactor r 0))
    have htailnorm : ‖metaplecticPrefactor r 0*
        ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤‖metaplecticPrefactor r 0‖*E := by
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
