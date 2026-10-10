import OAI.MathematicalPhysics.Transonic.Phase.Amplitude

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff

lemma GlobalProfile.w0_square (P : GlobalProfile) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    P.w0 t X^2=t^(-2*P.beta/3)*P.radialM (radiusSq X/t^2)^((1:ℝ)/3) := by
  rw [GlobalProfile.w0,← Real.rpow_mul_natCast (P.s0_timelike ht X).le]
  norm_num only [Nat.cast_ofNat,show (1/6:ℝ)*2=1/3 by norm_num]
  rw [P.minkowski_radial ht X,Real.mul_rpow (sq_nonneg _) (P.radialM_pos
    (div_nonneg (radiusSq_nonneg X) (sq_nonneg t))).le]
  have he : ((t^(-P.beta))^2)^((1:ℝ)/3)=t^(-2*P.beta/3) := by
    rw [← Real.rpow_mul_natCast ht.le,← Real.rpow_mul ht.le]
    congr 1
    norm_num
    ring
  rw [he]

lemma GlobalProfile.w0_inverse_fourth_scaled (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    P.w0 t X^(-4:ℤ)*(t^(-P.beta))^2=
      t^(-2*P.beta/3)*P.radialM (radiusSq X/t^2)^(-(2:ℝ)/3) := by
  rw [GlobalProfile.w0,← Real.rpow_mul_intCast (P.s0_timelike ht X).le]
  norm_num only [Int.cast_neg,Int.cast_ofNat,show (1/6:ℝ)*(-4)= -2/3 by norm_num]
  rw [P.minkowski_radial ht X,Real.mul_rpow (sq_nonneg _) (P.radialM_pos
    (div_nonneg (radiusSq_nonneg X) (sq_nonneg t))).le]
  have hq : 0<(t^(-P.beta))^2 := sq_pos_of_pos (Real.rpow_pos_of_pos ht _)
  have he : ((t^(-P.beta))^2)^(-(2:ℝ)/3)*(t^(-P.beta))^2=t^(-2*P.beta/3) := by
    conv_lhs => arg 2; rw [← Real.rpow_one ((t^(-P.beta))^2)]
    rw [← Real.rpow_add hq]
    norm_num only [show (-(2:ℝ)/3)+1=1/3 by norm_num]
    rw [← Real.rpow_mul_natCast ht.le,← Real.rpow_mul ht.le]
    congr 1
    norm_num
    ring
  calc
    _=(((t^(-P.beta))^2)^(-(2:ℝ)/3)*(t^(-P.beta))^2)*
      P.radialM (radiusSq X/t^2)^(-(2:ℝ)/3) := by ring_nf
    _=_ := by rw [he]; simp only [neg_div]

def radialTrial (a : ℝ) (f : ℝ → ℝ) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  t^a*f (radiusSq X/t^2)

lemma radialTrial_time {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (a : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    partialTime (radialTrial a f) t X=t^(a-1)*(a*f (radiusSq X/t^2)-
      2*(radiusSq X/t^2)*derivWithin f (Ici 0) (radiusSq X/t^2)) :=
  (radial_time_derivative hf a ht X).deriv

lemma radialTrial_space {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ici 0))
    (a : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) (j : Fin 4) :
    partialSpace (radialTrial a f) j t X=t^(a-1)*2*(X j/t)*
      derivWithin f (Ici 0) (radiusSq X/t^2) := by
  have hz : radiusSq (coordinateLine X j 0)/t^2∈Ici (0:ℝ) :=
    div_nonneg (radiusSq_nonneg _) (sq_nonneg t)
  have hd := (hf.differentiableOn (by simp) _ hz).hasDerivWithinAt.comp_hasDerivAt
    (h:=fun r => radiusSq (coordinateLine X j r)/t^2) 0
    ((radiusSq_coordinate_derivative X j).div_const (t^2))
    (Filter.Eventually.of_forall (fun r => div_nonneg (radiusSq_nonneg _) (sq_nonneg t)))
  have hp := hd.const_mul (t^a)
  simp only [Function.comp_apply,coordinateLine_zero] at hp
  change deriv (fun r => t^a*f (radiusSq (coordinateLine X j r)/t^2)) 0=_
  rw [hp.deriv]
  have ht' : t^a=t*t^(a-1) := by
    calc
      _=t^(1+(a-1)) := by congr 1; ring
      _=_ := by rw [Real.rpow_add ht,Real.rpow_one]
  rw [ht']
  field_simp [ne_of_gt ht]

end SepticProfile

end
end

end OAI
