import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeTermScaling

namespace OAI

/-! The entire prime-divisible part of the actual positive Gram integral.
After a common cube dilation it is the original finite denominator sum,
with the exact local multiplier and unchanged original cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGramPrimePart (p h k : Eisenstein) (W V : C_c(ℝ,ℂ)) (ε δ : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
    ∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => p∣c),
      cubicThetaGramKloostermanTerm h k V c v

theorem cubicThetaGramPrimePart_cube {p : Eisenstein} (hp : primaryPrime p)
    (h k : Eisenstein) (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    cubicThetaGramPrimePart p (p^3*h) (p^3*k)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) W)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) V)
      (ε/‖((p^3:Eisenstein):ℂ)‖) (δ/‖((p^3:Eisenstein):ℂ)‖)=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramCubeMultiplier p d*
          cubicThetaGramKloostermanTerm h k V d v := by
  let r := ‖((p^3:Eisenstein):ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))
  have hn : norm (p^3)=r^2 := Complex.normSq_eq_norm_sq _
  let F : ℝ → ℂ := fun v => star (W v)/(v:ℂ)^3*
    ∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramCubeMultiplier p d*
      cubicThetaGramKloostermanTerm h k V d v
  unfold cubicThetaGramPrimePart
  simp_rw [cubicThetaGramKloostermanTerm_cube_filter hp,
    cubicThetaGramDenominators_cube_sum hp hε hδ]
  have he : (∫ v in Ioi (ε/r),star (cubicThetaRadialWeightScale r hr W v)/(v:ℂ)^3*
      ∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm (p^3*h) (p^3*k)
        (cubicThetaRadialWeightScale r hr V) (p^3*d) v)=
      ∫ v in Ioi (ε/r),(r:ℂ)*F (r*v) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv0 : 0<v := (div_pos hε hr).trans hv
    have hrv : r*v/r=v := by field_simp
    have hs : (∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm (p^3*h) (p^3*k)
        (cubicThetaRadialWeightScale r hr V) (p^3*d) v)=
        (norm (p^3):ℂ)⁻¹*∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramCubeMultiplier p d*
          cubicThetaGramKloostermanTerm h k V d (r*v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨_,hd3,hd0⟩ := (cubicThetaGramDenominators_iff ε δ d).mp hd
      have ht := cubicThetaGramKloostermanTerm_cube_scale hp hd3 hd0 h k V (mul_pos hr hv0)
      change cubicThetaGramKloostermanTerm (p^3*h) (p^3*k)
        (cubicThetaRadialWeightScale r hr V) (p^3*d) (r*v/r)=_ at ht
      rw [hrv] at ht
      simpa only [mul_assoc] using ht
    dsimp only [F]
    change star (W (r*v))/(v:ℂ)^3*_=_
    rw [hs,hn]
    have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hvC : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv0.ne'
    push_cast
    field_simp
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi F (ε/r) hr]
  have hre : r*(ε/r)=ε := by field_simp
  rw [hre,Complex.real_smul]
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  rw [←mul_assoc,mul_inv_cancel₀ hrC,one_mul]

end CubicFirstMoment

end

end OAI
