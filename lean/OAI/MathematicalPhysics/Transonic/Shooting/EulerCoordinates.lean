import OAI.MathematicalPhysics.Transonic.Shooting.ShootingMatch

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set SourceFamily

/-- Inverse of the source Euler compactification, in the normalized radius. -/
def coord (z : ℝ) : ℝ := (1-z)/(501/500-z)
def endRadius (e : ℝ) : ℝ := 1+SourceEuler.changeOfVariable (1/500) e

lemma endRadius_bounds {e : ℝ} (he : 0<e) (helt : e<1/3) :
    99/100<endRadius e ∧ endRadius e<1 := by
  unfold endRadius SourceEuler.changeOfVariable
  have hd : 0<1-e := by linarith
  have hh : 0<(1/500:ℝ)*e/(1-e) := div_pos (by positivity) hd
  have hh' : (1/500:ℝ)*e/(1-e)<1/100 := by
    rw [div_lt_iff₀ hd]
    linarith
  simp only [neg_mul,neg_div]
  constructor <;> linarith

lemma coord_end {e : ℝ} (he : e<1) : coord (endRadius e)=e := by
  have hd : 1-e≠0 := by linarith
  unfold coord endRadius SourceEuler.changeOfVariable
  have hh : 501/500-(1+(-(1/500:ℝ)*e/(1-e)))=1/(500*(1-e)) := by field_simp;ring
  rw [hh]
  field_simp
  ring

lemma coord_range {e z : ℝ} (he : 0<e) (helt : e<1/3)
    (hz : z ∈ Icc (99/100:ℝ) (endRadius e)) : coord z ∈ Icc e (5/6) := by
  have hb := endRadius_bounds he helt
  have hzd : 0<(501/500:ℝ)-z := by linarith [hz.2]
  have hde : 0<1-e := by linarith
  have hexpr : endRadius e=1-(1/500)*e/(1-e) := by
    simp only [endRadius,SourceEuler.changeOfVariable,neg_mul,neg_div,sub_eq_add_neg]
  constructor
  · rw [coord,le_div_iff₀ hzd]
    have hzz := hz.2
    rw [hexpr] at hzz
    have heq : (1-z)*(1-e)≥(1/500)*e := by
      have hem : (1/500)*e/(1-e)≤1-z := by linarith
      exact (div_le_iff₀ hde).mp hem
    nlinarith
  · rw [coord,div_le_iff₀ hzd]
    linarith [hz.1]

lemma coord_ninety_nine : coord (99/100:ℝ)=5/6 := by norm_num [coord]

lemma coord_derivative {z : ℝ} (hz : z<1) :
    HasDerivAt coord (-(1/500)/(501/500-z)^2) z := by
  have hd : (501/500:ℝ)-z≠0 := by linarith
  convert ((hasDerivAt_const z 1).sub (hasDerivAt_id z)).div
    ((hasDerivAt_const z (501/500)).sub (hasDerivAt_id z)) hd using 1 <;>
    first | rfl | (congr 1;simp only [Pi.sub_apply,id_eq];ring)

lemma coord_field (sigma kappa z u : ℝ) (hz : z<1)
    (hD : AxisBarriers.D sigma z u≠0) :
    (EulerContinuation.N kappa (coord z) u/EulerContinuation.D sigma (coord z) u)*
      (-(1/500)/(501/500-z)^2)=AxisBarriers.N kappa z u/AxisBarriers.D sigma z u := by
  have hd : (501/500:ℝ)-z≠0 := by linarith
  have hd' : (501:ℝ)-z*500≠0 := by linarith
  have h1 : 1-(1+1/500:ℝ)*coord z=(1/500)*z/(501/500-z) := by
    unfold coord;field_simp [hd,hd'];ring_nf;field_simp [hd'];ring
  have h2 : 1-coord z=(1/500)/(501/500-z) := by unfold coord;field_simp [hd,hd'];ring
  have hde : EulerContinuation.D sigma (coord z) u=
      (1/500)^3*AxisBarriers.D sigma z u/(501/500-z)^3 := by
    unfold EulerContinuation.D
    rw [h1,h2]
    unfold AxisBarriers.D
    field_simp
  have hne : EulerContinuation.N kappa (coord z) u=
      -(1/500)^2*AxisBarriers.N kappa z u/(501/500-z) := by
    unfold EulerContinuation.N
    rw [h1,h2]
    unfold AxisBarriers.N
    field_simp
  rw [hde,hne]
  field_simp [hd,hd']
  ring_nf
  field_simp [hd']
  ring

end SepticProfile.SonicShooting

end
end

end OAI
