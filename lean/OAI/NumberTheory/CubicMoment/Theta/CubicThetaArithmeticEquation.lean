import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateRegularity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinSpectral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticRemainder

namespace OAI

/-! The actual arithmetic remainder satisfies the same forced spectral
operator as the continued global weak response. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

private lemma second_sub {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t-g t)) x=deriv (deriv f) x-deriv (deriv g) x := by
  have he : deriv (fun t => f t-g t)=ᶠ[𝓝 x] (fun t => deriv f t-deriv g t) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with t ht hu
    exact deriv_sub (ht.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))

lemma cubicThetaHyperbolicOperator_sub {F G : ℝ → ℝ → ℝ → ℂ} (x y v : ℝ)
    (hF : ∀ k, ContDiffAt ℝ 2 (cubicThetaAxisFunction F k x y v) (cubicThetaCoordinateCenter k x y v))
    (hG : ∀ k, ContDiffAt ℝ 2 (cubicThetaAxisFunction G k x y v) (cubicThetaCoordinateCenter k x y v)) :
    cubicThetaHyperbolicOperator (fun a b t => F a b t-G a b t) x y v=
      cubicThetaHyperbolicOperator F x y v-cubicThetaHyperbolicOperator G x y v := by
  have hx := second_sub (hF .x) (hG .x)
  have hy := second_sub (hF .y) (hG .y)
  have ht := second_sub (hF .height) (hG .height)
  have h₁ := deriv_sub ((hF .height).differentiableAt (by norm_num))
    ((hG .height).differentiableAt (by norm_num))
  dsimp only [cubicThetaAxisFunction,cubicThetaCoordinateCenter] at hx hy ht h₁
  change deriv (fun t => F x y t-G x y t) v=
    deriv (fun t => F x y t) v-deriv (fun t => G x y t) v at h₁
  unfold cubicThetaHyperbolicOperator
  rw [hx,hy,ht,h₁]
  ring

lemma cubicThetaIncomingEisenstein_coordinate_contDiffAt
    (k : CubicThetaAxis) (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingEisenstein (cubicThetaCoordinateLine k x y v t) s)
      (cubicThetaCoordinateCenter k x y v) := by
  have hp : 0<(cubicThetaCartesianPoint x y v).2 := hv
  have hi := (cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hline : ContDiffAt ℝ ∞ (cubicThetaCoordinateLine k x y v) (cubicThetaCoordinateCenter k x y v) := by
    cases k <;> unfold cubicThetaCoordinateLine cubicThetaCoordinateCenter cubicThetaCartesianPoint
    · exact ((Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const).contDiffAt
    · exact ((contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const).contDiffAt
    · exact (contDiff_const.prodMk contDiff_id).contDiffAt
  have hi' : ContDiffAt ℝ ∞ (fun p => cubicThetaIncomingEisenstein p s)
      (cubicThetaCoordinateLine k x y v (cubicThetaCoordinateCenter k x y v)) := by
    rw [cubicThetaCoordinateLine_center]
    exact hi
  have hj := hi'.comp (cubicThetaCoordinateCenter k x y v) hline
  simpa only [Function.comp_def,cubicThetaCoordinateLine_center] using hj.of_le (by norm_num : (2:ℕ∞ω)≤∞)

theorem cubicThetaArithmeticRemainder_equation {s : ℂ} (hs : 2<s.re)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaArithmeticRemainder (cubicThetaCartesianPoint a b t) s) x y v-
      s*(s-2)*cubicThetaArithmeticRemainder (cubicThetaCartesianPoint x y v) s=
        -cubicThetaForcingSeries (cubicThetaCartesianPoint x y v) s := by
  have hE k := cubicThetaEisenstein_coordinate_contDiffAt k s hs x y hv
  have hI k := cubicThetaIncomingEisenstein_coordinate_contDiffAt k s x y hv
  have he : ∀ k, ContDiffAt ℝ 2
      (cubicThetaAxisFunction (fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s) k x y v)
      (cubicThetaCoordinateCenter k x y v) := by
    intro k
    cases k with
    | x => exact hE .x
    | y => exact hE .y
    | height => exact hE .height
  have hi : ∀ k, ContDiffAt ℝ 2
      (cubicThetaAxisFunction (fun a b t => cubicThetaIncomingEisenstein (cubicThetaCartesianPoint a b t) s) k x y v)
      (cubicThetaCoordinateCenter k x y v) := by
    intro k
    cases k with
    | x => exact hI .x
    | y => exact hI .y
    | height => exact hI .height
  unfold cubicThetaArithmeticRemainder
  rw [cubicThetaHyperbolicOperator_sub
    (F:=fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s)
    (G:=fun a b t => cubicThetaIncomingEisenstein (cubicThetaCartesianPoint a b t) s) x y v he hi,
    cubicThetaEisenstein_eigenvalue s hs x y hv,cubicThetaIncomingEisenstein_equation s x y hv]
  ring

end CubicFirstMoment

end

end OAI
