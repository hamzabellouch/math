import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingGeometry
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSecantEnergy

namespace OAI

/-! Pointwise quadratic comparison of the two sampling orders. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalSamplingDifference (f : SchwartzMap (ℝ×ℝ) ℂ) (u : (ℝ×ℝ) → ℝ)
    (t s : ℝ) (z : ℝ×ℝ) : ℂ :=
  f (z.1-t,z.2-s-t*u (verticalTranslation s z))-
    f (z.1-t,z.2-s-t*u z)

theorem verticalSamplingDifference_energy_pointwise (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (t s : ℝ) (z : ℝ×ℝ) :
    ‖verticalSamplingDifference f u t s z‖^2≤
      (2*|t| *|s|)^2 * ∫ theta in (0:ℝ)..1,
        ‖verticalSchwartzDeriv f (verticalSampling (verticalBlend u s theta) t t s z)‖^2 := by
  have hu' := hu.dist_le_mul z (verticalTranslation s z)
  have hd : dist z (verticalTranslation s z)=|s| := by
    change dist z (z.1,z.2-s)=|s|
    simp only [Prod.dist_eq,Real.dist_eq,sub_self,abs_zero]
    rw [show z.2-(z.2-s)=s by ring,max_eq_right (abs_nonneg s)]
  rw [hd,Real.dist_eq] at hu'
  have hdelta : |(z.2-s-t*u (verticalTranslation s z))-(z.2-s-t*u z)|≤2*|t| *|s| := by
    have heq : (z.2-s-t*u (verticalTranslation s z))-(z.2-s-t*u z)=
        t*(u z-u (verticalTranslation s z)) := by ring
    rw [heq,abs_mul]
    calc
      _ ≤ |t| *(2*|s|) := mul_le_mul_of_nonneg_left hu' (abs_nonneg t)
      _ = _ := by ring
  have hpath (theta : ℝ) :
      (z.1-t,(z.2-s-t*u z)+theta*((z.2-s-t*u (verticalTranslation s z))-(z.2-s-t*u z)))=
        verticalSampling (verticalBlend u s theta) t t s z := by
    ext
    · rfl
    · dsimp [verticalSampling,verticalBlend]
      ring
  have h := vertical_secant_energy f (z.1-t) (z.2-s-t*u z)
    (z.2-s-t*u (verticalTranslation s z))
  simp_rw [hpath] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right
  · have hs := pow_le_pow_left₀ (abs_nonneg _) hdelta 2
    simpa only [sq_abs] using hs
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro theta htheta
    exact sq_nonneg _

end LipschitzHilbert.PacketRepresentation

end

end OAI
