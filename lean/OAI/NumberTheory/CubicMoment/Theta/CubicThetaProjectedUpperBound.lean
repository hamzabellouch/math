import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedDirichlet
import OAI.NumberTheory.CubicMoment.Estimates.ThetaUpperVerticalBound

namespace OAI

/-! Uniform vertical bounds for the two actual completed Mellin functions. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPairedUpper_bounded_strip (f g : ℝ→ℂ) (ε : ℂ) (k : ℕ)
    (hf : ∀ s, MellinConvergent (thetaUpper f) s)
    (hg : ∀ s, MellinConvergent (thetaUpper g) s) (a b : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖mellin (thetaUpper f) s+ε*mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s)‖≤C := by
  let B := ((2*k:ℕ):ℝ)-a
  refine ⟨thetaUpperNormMass f b+‖ε‖*thetaUpperNormMass g B,
    add_nonneg (thetaUpperNormMass_nonneg f b)
      (mul_nonneg (_root_.norm_nonneg ε) (thetaUpperNormMass_nonneg g B)),?_⟩
  intro s hs
  have hfb : ‖mellin (thetaUpper f) s‖≤thetaUpperNormMass f b :=
    thetaUpper_vertical_bound (hf b) hs.2
  have hgb : ‖mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s)‖≤thetaUpperNormMass g B := by
    apply thetaUpper_vertical_bound (hg B)
    simp only [Complex.sub_re,Complex.natCast_re]
    exact sub_le_sub_left hs.1 _
  exact (norm_add_le _ _).trans (add_le_add hfb (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hgb (_root_.norm_nonneg ε)))

theorem cubicThetaProjectedAngularCompleted_bounded_strip (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖cubicThetaProjectedAngularCompleted g hc rev k s‖≤C := by
  apply cubicThetaPairedUpper_bounded_strip
  · intro s
    exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) s
  · intro s
    exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) s

theorem cubicThetaSelectedAngularCompleted_bounded_strip (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖cubicThetaSelectedAngularCompleted g hc rev k s‖≤C := by
  apply cubicThetaPairedUpper_bounded_strip
  · intro s
    exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) s
  · intro s
    exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) s

end CubicFirstMoment

end

end OAI
