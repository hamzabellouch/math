import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSecondContinuity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAxisLineDerivative
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticEnergy

namespace OAI

/-! The literal arithmetic remainder has continuous pure second
coordinate derivatives and the corresponding actual line derivatives. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaAxisSecond_sub (k : CubicThetaAxis) (f g : ℂ × ℝ → ℂ) (p : ℂ × ℝ)
    (hf : ContDiffAt ℝ 2 (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2))
    (hg : ContDiffAt ℝ 2 (fun t => g (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    cubicThetaAxisSecond k (f-g) p=cubicThetaAxisSecond k f p-cubicThetaAxisSecond k g p := by
  let c := cubicThetaCoordinateCenter k p.1.re p.1.im p.2
  let F := fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)
  let G := fun t => g (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)
  have he : deriv (F-G)=ᶠ[𝓝 c] (fun t => deriv F t-deriv G t) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with t ht hu
    exact deriv_sub (ht.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num))
  change deriv (deriv (F-G)) c=deriv (deriv F) c-deriv (deriv G) c
  rw [he.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))

lemma cubicThetaArithmetic_axis_contDiffAt (k : CubicThetaAxis) {s : ℂ} (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ 2 (fun t => cubicThetaArithmeticRemainder
      (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) s)
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) :=
  (cubicThetaEisenstein_coordinate_contDiffAt k s hs p.1.re p.1.im hp).sub
    (cubicThetaIncomingEisenstein_coordinate_contDiffAt k s p.1.re p.1.im hp)

lemma cubicThetaArithmetic_axisSecond_continuous (k : CubicThetaAxis) {s : ℂ} (hs : 2<s.re) :
    ContinuousOn (cubicThetaAxisSecond k (fun p => cubicThetaArithmeticRemainder p s))
      {p : ℂ × ℝ | 0<p.2} := by
  have hE := cubicThetaEisenstein_axisSecond_continuous k hs
  have hI := cubicThetaAxisSecond_continuousOn k (fun p => cubicThetaIncomingEisenstein p s)
    (isOpen_lt continuous_const continuous_snd)
    ((cubicThetaIncomingEisenstein_contDiffOn s).of_le (by norm_num : (2:ℕ∞ω)≤∞))
  apply (hE.sub hI).congr
  intro p hp
  exact cubicThetaAxisSecond_sub k (fun q => cubicThetaEisenstein q s)
    (fun q => cubicThetaIncomingEisenstein q s) p
    (cubicThetaEisenstein_coordinate_contDiffAt k s hs p.1.re p.1.im hp)
    (cubicThetaIncomingEisenstein_coordinate_contDiffAt k s p.1.re p.1.im hp)

lemma cubicThetaArithmetic_axis_hasLineDerivAt (k : CubicThetaAxis) {s : ℂ} (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    HasLineDerivAt ℝ (cubicThetaAxisFirst k (fun q => cubicThetaArithmeticRemainder q s))
      (cubicThetaAxisSecond k (fun q => cubicThetaArithmeticRemainder q s) p) p (cubicThetaAxisVector k) :=
  cubicThetaAxisFirst_hasLineDerivAt k _ p (cubicThetaArithmetic_axis_contDiffAt k hs hp)

end CubicFirstMoment

end

end OAI
