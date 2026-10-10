import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleLimit
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticPlane

namespace OAI

/-! The constant mode disappears from every positive small-circle coefficient. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

lemma cubicThetaCircle_coefficient_const_add (c : ℂ) {f : AddCircle (1:ℝ)→ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) {k : ℤ} (hk : k≠0) :
    fourierCoeff (fun t => c+f t) k=fourierCoeff f k := by
  have he : (fun _ : AddCircle (1:ℝ) => c)=fun t => c*fourier 0 t := by
    funext t
    simp
  have hz : fourierCoeff (fun _ : AddCircle (1:ℝ) => c) k=0 := by
    rw [he,fourierCoeff.const_mul]
    simp [fourierCoeff_fourier,hk]
  have h := congrFun (fourierCoeff.add (integrable_const c) hf) k
  have ha : (fun t => c+f t)=(fun _ : AddCircle (1:ℝ) => c)+f := by
    funext t
    rfl
  rw [ha]
  simpa only [Pi.add_apply,hz,zero_add] using h

lemma cubicThetaArithmeticPlane_circle_coefficient (z d : ℂ) {v : ℝ} (hv : 0<v)
    (r : ℝ) (rev : Bool) {k : ℕ} (hk : 0<k) :
    fourierCoeff (fun t => cubicThetaArithmeticPlane (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ)=
      fourierCoeff (fun t => cubicThetaNonconstant cubicThetaArithmeticCoefficient
        (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ) := by
  have hzero := cubicThetaAngular_summable (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound 0 hv z
  have ha0 : cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient 0=
      cubicThetaArithmeticCoefficient := by
    funext n
    simp [cubicThetaAngularCoefficient,theta]
  rw [ha0] at hzero
  have hf : Continuous (fun t => cubicThetaNonconstant cubicThetaArithmeticCoefficient
      (z+cubicThetaSignedCircle rev d r t,v)) := by
    rw [cubicThetaCircleActual_series]
    exact cubicThetaCircleSeries_continuous hzero.norm r
  change fourierCoeff (fun t => cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (z+cubicThetaSignedCircle rev d r t,v)) (k:ℤ)=_
  exact cubicThetaCircle_coefficient_const_add _
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (by exact_mod_cast hk.ne')

theorem cubicThetaArithmeticPlane_circle_limit (z : ℂ) (rev : Bool) {k : ℕ} (hk : 0<k)
    {d : ℝ→ℂ} {v : ℝ→ℝ} {d₀ : ℂ} {v₀ : ℝ}
    (hd : Tendsto d (𝓝[Set.Ioi 0] 0) (𝓝 d₀))
    (hv : Tendsto v (𝓝[Set.Ioi 0] 0) (𝓝 v₀)) (hv₀ : 0<v₀) :
    Tendsto (fun r : ℝ => fourierCoeff
      (fun t => cubicThetaArithmeticPlane (z+cubicThetaSignedCircle rev (d r) r t,v r))
        (k:ℤ)/(r:ℂ)^k) (𝓝[Set.Ioi 0] 0)
      (𝓝 (((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d₀)^k*
        cubicThetaNonconstant
          (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k)) (z,v₀))) := by
  have H := cubicThetaCircleActual_limit (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound z rev k hd hv hv₀
  apply H.congr'
  filter_upwards [hv.eventually (lt_mem_nhds hv₀)] with r hr
  rw [cubicThetaArithmeticPlane_circle_coefficient z (d r) hr r rev hk]

end CubicFirstMoment

end

end OAI
