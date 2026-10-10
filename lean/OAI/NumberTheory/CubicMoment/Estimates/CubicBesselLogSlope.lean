import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselLogDerivative
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerDerivative

namespace OAI

/-! Positivity and a strict slope estimate for the fixed Bessel kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselLogIntegral_pos {a : ℝ} (ha : 0<a) :
    0<∫ u : ℝ,cubicBesselLogWeight a u := by
  rw [integral_pos_iff_support_of_nonneg
    (fun u => (cubicBesselLogWeight_pos a u).le) (cubicBesselLogWeight_integrable ha)]
  have hs : Function.support (cubicBesselLogWeight a)=univ := by
    ext u
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (cubicBesselLogWeight_pos a u).ne'
  rw [hs]
  simp

lemma cubicBesselLogIntegral_slope {a : ℝ} (ha : 0<a) :
    (∫ u : ℝ,cubicBesselLogDerivative a u)≤ -2*(∫ u : ℝ,cubicBesselLogWeight a u) := by
  rw [←integral_const_mul]
  apply integral_mono (cubicBesselLogDerivative_integrable ha)
    ((cubicBesselLogWeight_integrable ha).const_mul (-2))
  intro u
  unfold cubicBesselLogDerivative
  have hw := cubicBesselLogWeight_pos a u
  have hc := Real.one_le_cosh u
  nlinarith

lemma cubicBesselKernelDerivative_log {a : ℝ} (ha : 0<a) :
    2*a*cubicBesselKernelDerivative (a^2)=∫ u : ℝ,cubicBesselLogDerivative a u := by
  have hp : HasDerivAt (fun x : ℝ => x^2) (2*a) a := by
    convert (hasDerivAt_id a).pow 2 using 1
    · funext x; rfl
    · norm_num [id_eq]
  have hK := (cubicBesselKernel_hasDerivAt (sq_pos_of_pos ha)).comp_of_eq a hp rfl
  have hI := cubicBesselLogIntegral_hasDerivAt ha
  have he : (fun x : ℝ => cubicBesselKernel (x^2))=ᶠ[𝓝 a]
      (fun x => ∫ u : ℝ,cubicBesselLogWeight x u) := by
    filter_upwards [show Ioi (0:ℝ)∈𝓝 a from Ioi_mem_nhds ha] with x hx
    exact cubicBesselKernel_log hx
  have h := hK.unique (hI.congr_of_eventuallyEq he)
  simpa only [pow_one,mul_one,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using h

lemma cubicThetaWhittakerDerivative_re_neg {v : ℝ} (hv : 0<v)
    (hvπ : 1<4*Real.pi*v) : (cubicThetaWhittakerDerivative v).re<0 := by
  let a := 2*Real.pi*v
  have ha : 0<a := by dsimp [a]; positivity
  let I := ∫ u : ℝ,cubicBesselLogWeight a u
  let J := ∫ u : ℝ,cubicBesselLogDerivative a u
  have hI : 0<I := cubicBesselLogIntegral_pos ha
  have hJ : J≤ -2*I := cubicBesselLogIntegral_slope ha
  have hK : cubicBesselKernel (a^2)=I := cubicBesselKernel_log ha
  have hD : 2*a*cubicBesselKernelDerivative (a^2)=J := cubicBesselKernelDerivative_log ha
  have hle := mul_le_mul_of_nonneg_left hJ (show 0≤a/2 by positivity)
  change cubicBesselKernel (a^2)/2+a^2*cubicBesselKernelDerivative (a^2)<0
  rw [hK]
  have hid : a^2*cubicBesselKernelDerivative (a^2)=(a/2)*J := by rw [←hD]; ring
  rw [hid]
  have hcoef : 1<2*a := by dsimp [a]; nlinarith
  nlinarith [mul_pos (show 0<2*a-1 by linarith) hI]

end CubicFirstMoment

end

end OAI
