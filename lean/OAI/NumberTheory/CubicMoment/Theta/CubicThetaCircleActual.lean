import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleNormalized
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleTrace
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointMajorant

namespace OAI

/-! Small-circle coefficients of the actual fixed-height theta series.
Both orientations retain their precise signed angular coefficients. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

def cubicThetaCircleOrder (rev : Bool) (k : ℕ) : ℤ := if rev then -(k:ℤ) else (k:ℤ)
def cubicThetaCircleMultiplier (rev : Bool) (d : ℂ) : ℂ := if rev then star d else d
def cubicThetaCircleFrequency (rev : Bool) (d : ℂ) (n : Eisenstein) : ℂ :=
  if rev then star (cubicThetaFrequency n*d) else cubicThetaFrequency n*d
def cubicThetaSignedCircle (rev : Bool) (d : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) : ℂ :=
  (r:ℂ)*d*fourier (if rev then -1 else 1) t

lemma cubicThetaCircleActual_series (a : Eisenstein→ℂ) (z d : ℂ) (r v : ℝ) (rev : Bool) :
    (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev d r t,v))=
      cubicThetaCircleSeries (cubicThetaSeriesTerm a z v) (cubicThetaCircleFrequency rev d) r := by
  funext t
  apply tsum_congr
  intro n
  cases rev
  · exact cubicThetaSeriesTerm_circle a z d r v n t
  · exact cubicThetaSeriesTerm_circle_reverse a z d r v n t

lemma cubicThetaCircleActual_power (a : Eisenstein→ℂ) (z d : ℂ) (v : ℝ)
    (rev : Bool) (n : Eisenstein) (k : ℕ) :
    cubicThetaSeriesTerm a z v n*(cubicThetaCircleFrequency rev d n)^k=
      (cubicThetaCircleMultiplier rev d)^k*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) z v n := by
  cases rev
  · change cubicThetaSeriesTerm a z v n*(cubicThetaFrequency n*d)^k=
      d^k*cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (k:ℤ)) z v n
    rw [mul_pow,←cubicThetaSeriesTerm_frequency_power]
    ring
  · change cubicThetaSeriesTerm a z v n*(star (cubicThetaFrequency n*d))^k=
      (star d)^k*cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-(k:ℤ))) z v n
    rw [star_mul,mul_pow,←cubicThetaSeriesTerm_conj_frequency_power]
    ring

lemma cubicThetaCircleActual_power_norm (a : Eisenstein→ℂ) (z d : ℂ) (v : ℝ)
    (rev : Bool) (n : Eisenstein) (k : ℕ) :
    ‖cubicThetaSeriesTerm a z v n‖*‖cubicThetaCircleFrequency rev d n‖^k=
      ‖d‖^k*‖cubicThetaSeriesTerm
        (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) z v n‖ := by
  have h := congrArg (fun x : ℂ => ‖x‖) (cubicThetaCircleActual_power a z d v rev n k)
  simp only [norm_mul,norm_pow] at h
  cases rev <;> simpa [cubicThetaCircleMultiplier] using h

lemma cubicThetaCircleActual_summable {a : Eisenstein→ℂ} {C : ℝ} (hC : 0≤C)
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n) (z d : ℂ) {v : ℝ} (hv : 0<v)
    (rev : Bool) (k : ℕ) :
    Summable (fun n => cubicThetaSeriesTerm a z v n*(cubicThetaCircleFrequency rev d n)^k) := by
  have h := (cubicThetaAngular_summable hC ha (cubicThetaCircleOrder rev k) hv z).mul_left
    ((cubicThetaCircleMultiplier rev d)^k)
  exact h.congr (fun n => (cubicThetaCircleActual_power a z d v rev n k).symm)

theorem cubicThetaCircleActual_remainder {a : Eisenstein→ℂ} {C : ℝ} (hC : 0≤C)
    (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n) (z d : ℂ) {v : ℝ} (hv : 0<v)
    (rev : Bool) (k : ℕ) {r : ℝ} (hr : 0<r) :
    ‖fourierCoeff (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev d r t,v))
        (k:ℤ)/(r:ℂ)^k-
      ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v)‖≤
      (((4*Real.pi)^(k+1)/(k.factorial:ℝ))*‖d‖^(k+1)*
        ∑' n, ‖cubicThetaSeriesTerm
          (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖)*r := by
  have hzero := cubicThetaAngular_summable hC ha 0 hv z
  have ha0 : cubicThetaAngularCoefficient a 0=a := by
    funext n
    simp [cubicThetaAngularCoefficient,theta]
  rw [ha0] at hzero
  have hk := cubicThetaCircleActual_summable hC ha z d hv rev k
  have hk1 := (cubicThetaCircleActual_summable hC ha z d hv rev (k+1)).norm
  simp only [norm_mul,norm_pow] at hk1
  have H := cubicThetaCircleSeries_normalized_remainder hzero.norm k hk hk1 hr
  rw [←cubicThetaCircleActual_series a z d r v rev] at H
  have he : (∑' n, cubicThetaSeriesTerm a z v n*(cubicThetaCircleFrequency rev d n)^k)=
      (cubicThetaCircleMultiplier rev d)^k*
        cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v) := by
    simp_rw [cubicThetaCircleActual_power,tsum_mul_left]
    rfl
  have hm : (∑' n, ‖cubicThetaSeriesTerm a z v n‖*‖cubicThetaCircleFrequency rev d n‖^(k+1))=
      ‖d‖^(k+1)*∑' n, ‖cubicThetaSeriesTerm
        (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖ := by
    simp_rw [cubicThetaCircleActual_power_norm,tsum_mul_left]
  rw [he,hm] at H
  simpa only [mul_assoc] using H

end CubicFirstMoment

end

end OAI
