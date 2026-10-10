import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCodeMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticScaledAmplitude

namespace OAI

/-! Apply the two scalar estimates to the literal prefix amplitude.
The resulting weights are the geometric and primary norm weights already
controlled by the finite arithmetic prefix sums. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_min_common {R H P : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    min R (H*P) ≤ Real.sqrt (R*(H*P)) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [pow_two] using mul_le_mul (min_le_left R (H*P))
    (min_le_right R (H*P)) (le_min hR (mul_nonneg hH hP)) hR

lemma metaplectic_first_norm_weight {D P : ℝ} (hP : 0 ≤ P) :
    D^(-1:ℝ)*P^(-(1/2):ℝ) = 1/(D*Real.sqrt P) := by
  rw [Real.rpow_neg_one,Real.rpow_neg hP,←Real.sqrt_eq_rpow]
  ring

lemma metaplectic_second_norm_weight {D P : ℝ} (hD : 0 < D) (hP : 0 < P) :
    D^(-(5/2):ℝ)*P^(-(3/2):ℝ) = 1/(D^2*Real.sqrt D*P*Real.sqrt P) := by
  have hd : D^(5/2:ℝ) = D^2*Real.sqrt D := by
    rw [show (5/2:ℝ)=2+1/2 by ring,Real.rpow_add hD,Real.rpow_two,←Real.sqrt_eq_rpow]
  have hp : P^(3/2:ℝ) = P*Real.sqrt P := by
    rw [show (3/2:ℝ)=1+1/2 by ring,Real.rpow_add hP,Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hD.le,Real.rpow_neg hP.le,hd,hp]
  ring

lemma metaplecticPrefixAmplitude_nonneg {r : Eisenstein} (hr : primary r)
    {C : ℝ} (hC : 0 ≤ C) (p : MetaplecticDyadPrefix r) :
    0 ≤ metaplecticPrefixAmplitude r C p := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  unfold metaplecticPrefixAmplitude
  change 0 ≤ C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2)*
    min (norm r) (norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2)/_
  positivity

lemma metaplectic_prefix_first_amplitude {r : Eisenstein} (hr : primary r)
    {C : ℝ} (hC : 0 ≤ C) (p : MetaplecticDyadPrefix r) :
    metaplecticPrefixAmplitude r C p/Real.sqrt (norm r) ≤
      C*Real.sqrt 3*((3:ℝ)^(-1/6:ℝ))^p.2.1*
        (norm p.1^(-1:ℝ)*norm p.2.2.2.2^(-(1/2):ℝ)) := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb : 0 < (3:ℝ)^((p.2.1:ℝ)-1) := by positivity
  have ha : 0 ≤ (3:ℝ)^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ) := by positivity
  have hratio := div_le_div_of_nonneg_right (metaplectic_ramified_exponent_le p.2.1)
    (Real.sqrt_nonneg ((3:ℝ)^((p.2.1:ℝ)-1)))
  rw [metaplectic_ramified_first_ratio] at hratio
  have he := metaplectic_first_scaled_amplitude hR hh hp hd hb hC ha
    (metaplectic_min_common hR.le hh.le hp.le)
  change metaplecticPrefixAmplitude r C p/Real.sqrt (norm r) ≤ _
  calc
    _ ≤ (C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/
        Real.sqrt ((3:ℝ)^((p.2.1:ℝ)-1)))/(norm p.1*Real.sqrt (norm p.2.2.2.2)) := by
      simpa only [metaplecticPrefixAmplitude,metaplecticDivisorPrimary] using he
    _ = C*(3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/
        Real.sqrt ((3:ℝ)^((p.2.1:ℝ)-1)))*
          (1/(norm p.1*Real.sqrt (norm p.2.2.2.2))) := by ring
    _ ≤ C*(Real.sqrt 3*((3:ℝ)^(-1/6:ℝ))^p.2.1)*
        (1/(norm p.1*Real.sqrt (norm p.2.2.2.2))) := by
      gcongr
    _ = _ := by rw [←metaplectic_first_norm_weight hp.le]; ring

lemma metaplectic_prefix_second_amplitude {r : Eisenstein} (hr : primary r)
    {C : ℝ} (hC : 0 ≤ C) (p : MetaplecticDyadPrefix r) (I T : ℝ) :
    metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
        Real.sqrt (2*(I/metaplecticFreeScale p)/T) ≤
      C*3*((3:ℝ)^(-2/3:ℝ))^p.2.1*Real.sqrt (2*I/(norm r*T))*
        (norm p.1^(-(5/2):ℝ)*norm p.2.2.2.2^(-(3/2):ℝ)) := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hb : 0 < (3:ℝ)^((p.2.1:ℝ)-1) := by positivity
  have ha : 0 ≤ (3:ℝ)^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ) := by positivity
  have hratio := div_le_div_of_nonneg_right (metaplectic_ramified_exponent_le p.2.1) hb.le
  rw [metaplectic_ramified_second_ratio] at hratio
  have he := metaplectic_second_scaled_amplitude hR hh hp hd hb hC ha
    (min_le_right (norm r) (norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2))
    (I := I) (T := T)
  calc
    _ ≤ C*(3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/((3:ℝ)^((p.2.1:ℝ)-1)))*
        Real.sqrt (2*I/(norm r*T))/
          (norm p.1^2*Real.sqrt (norm p.1)*norm p.2.2.2.2*Real.sqrt (norm p.2.2.2.2)) := by
      simpa only [metaplecticPrefixAmplitude,metaplecticFreeScale,metaplecticDivisorPrimary] using he
    _ = C*(3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)/((3:ℝ)^((p.2.1:ℝ)-1)))*
        Real.sqrt (2*I/(norm r*T))*
          (1/(norm p.1^2*Real.sqrt (norm p.1)*norm p.2.2.2.2*Real.sqrt (norm p.2.2.2.2))) := by ring
    _ ≤ C*(3*((3:ℝ)^(-2/3:ℝ))^p.2.1)*Real.sqrt (2*I/(norm r*T))*
        (1/(norm p.1^2*Real.sqrt (norm p.1)*norm p.2.2.2.2*Real.sqrt (norm p.2.2.2.2))) := by
      gcongr
    _ = _ := by rw [←metaplectic_second_norm_weight hd hp]; ring

end CubicFirstMoment

end

end OAI
