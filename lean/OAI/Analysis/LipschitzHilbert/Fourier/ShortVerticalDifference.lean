import OAI.Analysis.LipschitzHilbert.Fourier.VerticalProjectionDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeL1

namespace OAI

/-! The exact vertical FTC for replacing short directional sampling by
horizontal sampling. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortVerticalDifference (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (t : ℝ) (z : ℝ×ℝ) : ℂ :=
  f (z.1-t,z.2-t*u z)-f (z.1-t,z.2)

theorem shortVerticalDifference_identity (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (t : ℝ) (z : ℝ×ℝ) :
    shortVerticalDifference f u t z=(-t*u z) •
      ∫ theta in Ioc (0:ℝ) 1, verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z) := by
  let d := -t*u z
  let H := fun theta : ℝ => verticalSchwartzDeriv f (z.1-t,z.2+theta*d)
  have hc : Continuous H := (verticalSchwartzDeriv f).continuous.comp (by fun_prop)
  have hi : IntervalIntegrable (fun theta => d • H theta) volume 0 1 :=
    ((continuous_const : Continuous (fun _ : ℝ => d)).smul hc).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _ => verticalPath_hasDerivAt f (z.1-t) z.2 d theta) hi
  have heq : shortVerticalDifference f u t z=d • ∫ theta in (0:ℝ)..1, H theta := by
    simpa only [shortVerticalDifference,zero_mul,add_zero,one_mul,
      show z.2+d=z.2-t*u z by dsimp [d]; ring,intervalIntegral.integral_smul] using h.symm
  rw [heq,intervalIntegral.integral_of_le zero_le_one]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with theta
  change verticalSchwartzDeriv f (z.1-t,z.2+theta*(-t*u z))=
    verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)
  rw [show z.2+theta*(-t*u z)=z.2-theta*t*u z by ring]

theorem shortVerticalDifference_norm (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : ∀ z, |u z|≤1) (t : ℝ) (z : ℝ×ℝ) :
    ‖shortVerticalDifference f u t z‖≤|t| *
      ∫ theta in Ioc (0:ℝ) 1, ‖verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)‖ := by
  rw [shortVerticalDifference_identity,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
  calc
    _ ≤ (|t| *|u z|)*∫ theta in Ioc (0:ℝ) 1,
        ‖verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_of_le_one_right (abs_nonneg _) (hu z)
      · exact integral_nonneg fun _ => norm_nonneg _

theorem shortVerticalDifference_uniform (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : ∀ z, |u z|≤1) (t C : ℝ)
    (hC : ∀ z, ‖verticalSchwartzDeriv f z‖≤C) (z : ℝ×ℝ) :
    ‖shortVerticalDifference f u t z‖≤|t| *C := by
  apply (shortVerticalDifference_norm f u hu t z).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hi : Integrable (fun theta : ℝ =>
      ‖verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)‖) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((verticalSchwartzDeriv f).continuous.comp (by fun_prop)).norm.intervalIntegrable 0 1 |>.1
  have h := integral_mono hi (integrable_const C) (fun theta => hC _)
  simpa only [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul] using h

theorem scaledSlope_lipschitz (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) :
    LipschitzWith 2 (fun z => theta*u z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := hu.dist_le_mul z w
  rw [Real.dist_eq] at h ⊢
  rw [←mul_sub,abs_mul,abs_of_nonneg h0]
  calc
    _ ≤ theta*(2*dist z w) := mul_le_mul_of_nonneg_left h h0
    _ ≤ 2*dist z w := mul_le_of_le_one_left (by positivity) h1

end LipschitzHilbert.PacketRepresentation

end

end OAI
