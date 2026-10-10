import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope

namespace OAI

/-! A normalized integrable envelope for the two endpoint errors in a
sharp time truncation. Its integral is independent of its radius. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def timeErrorEnvelope (r t : ℝ) : ℝ := r/(r^2+t^2)

theorem timeErrorEnvelope_nonneg (r t : ℝ) (hr : 0<r) : 0≤timeErrorEnvelope r t := by
  unfold timeErrorEnvelope
  positivity

theorem timeErrorEnvelope_eq (r t : ℝ) (hr : 0<r) :
    timeErrorEnvelope r t=r⁻¹*lineEnvelope 0 r 1 t := by
  unfold timeErrorEnvelope lineEnvelope
  simp only [sub_zero,pow_one]
  have hden : r^2+t^2≠0 := ne_of_gt (by positivity)
  have hden' : 1+(t/r)^2≠0 := ne_of_gt (by positivity)
  field_simp

theorem timeErrorEnvelope_integrable (r : ℝ) (hr : 0<r) :
    Integrable (timeErrorEnvelope r) := by
  have h := (integrable_lineEnvelope_one 0 r hr).const_mul r⁻¹
  simpa only [←timeErrorEnvelope_eq r _ hr] using h

theorem timeErrorEnvelope_integral (r : ℝ) (hr : 0<r) :
    (∫ t, timeErrorEnvelope r t)=Real.pi := by
  simp_rw [timeErrorEnvelope_eq r _ hr]
  rw [integral_const_mul,integral_lineEnvelope_one 0 r hr]
  field_simp

theorem timeErrorEnvelope_small (r t : ℝ) (hr : 0<r) (ht : |t|≤r) :
    r⁻¹≤2*timeErrorEnvelope r t := by
  have ht2 : t^2≤r^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ (abs_nonneg t) ht 2]
  have hd : 0<r^2+t^2 := by positivity
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hd).2
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hr).2
  nlinarith

theorem timeErrorEnvelope_large (r t : ℝ) (hr : 0<r) (ht : r≤|t|) :
    r/t^2≤2*timeErrorEnvelope r t := by
  have ht2 : r^2≤t^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ hr.le ht 2]
  have hd : 0<r^2+t^2 := by positivity
  have htpos : 0<t^2 := lt_of_lt_of_le (sq_pos_of_pos hr) ht2
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ htpos hd).2
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
