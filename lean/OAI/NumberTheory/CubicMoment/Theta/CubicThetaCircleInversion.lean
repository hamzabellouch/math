import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleActual
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionGeometry

namespace OAI

/-! Inversion takes every horizontal circle to a reversed horizontal circle.
Its transformed height depends only on the radius. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def cubicThetaCircleDualDirection (q : ℂ) (v r : ℝ) : ℂ :=
  -1/(q^2*((r^2+v^2:ℝ):ℂ))

def cubicThetaCircleDualHeight (q : ℂ) (v r : ℝ) : ℝ :=
  v/(Complex.normSq q*(r^2+v^2))

lemma cubicThetaSignedCircle_radius (rev : Bool) (r v : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaRadius (cubicThetaSignedCircle rev 1 r t,v)=r^2+v^2 := by
  have hn : Complex.normSq (fourier (if rev then -1 else 1) t)=1 := by
    rw [Complex.normSq_eq_norm_sq,fourier_apply,Circle.norm_coe,one_pow]
  simp only [cubicThetaRadius,cubicThetaSignedCircle,mul_one,Complex.normSq_mul,
    Complex.normSq_ofReal,hn,mul_one]
  ring

theorem cubicThetaInversion_circle (q : ℂ) (rev : Bool) (r v : ℝ) (t : AddCircle (1:ℝ)) :
    cubicThetaInversion q (cubicThetaSignedCircle rev 1 r t,v)=
      (cubicThetaSignedCircle (!rev) (cubicThetaCircleDualDirection q v r) r t,
        cubicThetaCircleDualHeight q v r) := by
  apply Prod.ext
  · change -star (cubicThetaSignedCircle rev 1 r t)/
      (q^2*(cubicThetaRadius (cubicThetaSignedCircle rev 1 r t,v):ℂ))=_
    rw [cubicThetaSignedCircle_radius]
    cases rev <;>
      simp only [cubicThetaSignedCircle,cubicThetaCircleDualDirection,Bool.not_false,
        Bool.not_true,Bool.false_eq_true,ite_false,ite_true,mul_one,star_mul,
        Complex.star_def,Complex.conj_ofReal,fourier_neg,starRingEnd_self_apply]
    all_goals ring
  · change v/(Complex.normSq q*cubicThetaRadius (cubicThetaSignedCircle rev 1 r t,v))=_
    rw [cubicThetaSignedCircle_radius]
    rfl

lemma cubicThetaCircleDualDirection_limit {q : ℂ} (hq : q≠0) {v : ℝ} (hv : 0<v) :
    Tendsto (cubicThetaCircleDualDirection q v) (𝓝[Set.Ioi 0] 0)
      (𝓝 (-1/(q^2*(v:ℂ)^2))) := by
  have hn : q^2*((0^2+v^2:ℝ):ℂ)≠0 := by
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add,Complex.ofReal_pow]
    exact mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hv.ne'))
  have hc : ContinuousAt (cubicThetaCircleDualDirection q v) 0 := by
    exact continuousAt_const.div (continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_id.pow 2).add_const (v^2)))) hn
  simpa [cubicThetaCircleDualDirection] using hc.tendsto.mono_left nhdsWithin_le_nhds

lemma cubicThetaCircleDualHeight_limit {q : ℂ} (hq : q≠0) {v : ℝ} (hv : 0<v) :
    Tendsto (cubicThetaCircleDualHeight q v) (𝓝[Set.Ioi 0] 0)
      (𝓝 ((Complex.normSq q*v)⁻¹)) := by
  have hn : Complex.normSq q*(0^2+v^2)≠0 := by
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add]
    exact mul_ne_zero (Complex.normSq_pos.mpr hq).ne' (pow_ne_zero _ hv.ne')
  have hc : ContinuousAt (cubicThetaCircleDualHeight q v) 0 :=
    continuousAt_const.div (continuousAt_const.mul ((continuousAt_id.pow 2).add_const (v^2))) hn
  have he : cubicThetaCircleDualHeight q v 0=(Complex.normSq q*v)⁻¹ := by
    dsimp [cubicThetaCircleDualHeight]
    norm_num only [zero_pow,zero_add]
    field_simp
  rw [←he]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
