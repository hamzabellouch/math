import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingGenerator

namespace OAI

/-! A proof-independent inverse family, with quantitative continuity in
space and time. These identities are used in the conjugation derivative. -/
noncomputable section
open Function
namespace LipschitzHilbert.PacketRepresentation

def lineSamplingInverse (u : ℝ → ℝ) (t : ℝ) : ℝ → ℝ := invFun (lineSampling u t)

theorem lineSamplingInverse_eq (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    lineSamplingInverse u t=(lineSamplingHomeomorph u hu B hB hb t ht).symm := by
  exact invFun_eq_of_injective_of_rightInverse (lineSampling_antilipschitz u hu t ht).injective
    (lineSamplingHomeomorph u hu B hB hb t ht).apply_symm_apply

theorem lineSampling_inverse_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (y : ℝ) :
    lineSampling u t (lineSamplingInverse u t y)=y :=
  rightInverse_invFun (lineSampling_surjective u hu.continuous B hB hb t) y

theorem lineSamplingInverse_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) (y : ℝ) :
    lineSamplingInverse u t (lineSampling u t y)=y :=
  leftInverse_invFun (lineSampling_antilipschitz u hu t ht).injective y

theorem lineSamplingInverse_space_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    LipschitzWith 2 (lineSamplingInverse u t) := by
  rw [lineSamplingInverse_eq u hu B hB hb t ht]
  exact lineSamplingHomeomorph_symm_lipschitz u hu B hB hb t ht

theorem lineSamplingInverse_displacement (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (y : ℝ) :
    |lineSamplingInverse u t y-y|≤|t| *B := by
  have he := lineSampling_inverse_apply u hu B hB hb t y
  unfold lineSampling at he
  have hid : lineSamplingInverse u t y-y=t*u (lineSamplingInverse u t y) := by linarith
  rw [hid,abs_mul]
  exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg t)

theorem lineSamplingInverse_time_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (s t : ℝ)
    (hs : |s|≤1/2) (y : ℝ) :
    |lineSamplingInverse u s y-lineSamplingInverse u t y|≤2*B*|s-t| := by
  have hh := (lineSampling_antilipschitz u hu s hs).le_mul_dist
    (lineSamplingInverse u s y) (lineSamplingInverse u t y)
  have hleft := lineSampling_inverse_apply u hu B hB hb s y
  have hright := lineSampling_inverse_apply u hu B hB hb t y
  have he : lineSampling u s (lineSamplingInverse u t y)=
      y+(t-s)*u (lineSamplingInverse u t y) := by
    unfold lineSampling at hright ⊢
    linarith
  rw [hleft,he] at hh
  simp only [Real.dist_eq,NNReal.coe_ofNat] at hh
  have habs : |y-(y+(t-s)*u (lineSamplingInverse u t y))|=
      |s-t| *|u (lineSamplingInverse u t y)| := by
    rw [show y-(y+(t-s)*u (lineSamplingInverse u t y))=(s-t)*u (lineSamplingInverse u t y) by ring,abs_mul]
  rw [habs] at hh
  have hb' := mul_le_mul_of_nonneg_left (hb (lineSamplingInverse u t y)) (abs_nonneg (s-t))
  nlinarith

theorem lineSamplingInverse_time_pointwise (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (s t : ℝ)
    (hs : |s|≤1/2) (y : ℝ) :
    |lineSamplingInverse u s y-lineSamplingInverse u t y|≤
      2*|s-t| *|u (lineSamplingInverse u t y)| := by
  have hh := (lineSampling_antilipschitz u hu s hs).le_mul_dist
    (lineSamplingInverse u s y) (lineSamplingInverse u t y)
  have hleft := lineSampling_inverse_apply u hu B hB hb s y
  have hright := lineSampling_inverse_apply u hu B hB hb t y
  have he : lineSampling u s (lineSamplingInverse u t y)=
      y+(t-s)*u (lineSamplingInverse u t y) := by
    unfold lineSampling at hright ⊢
    linarith
  rw [hleft,he] at hh
  simp only [Real.dist_eq,NNReal.coe_ofNat] at hh
  have hid : y-(y+(t-s)*u (lineSamplingInverse u t y))=
      (s-t)*u (lineSamplingInverse u t y) := by ring
  simpa only [hid,abs_mul,mul_assoc] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
