import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelAngularMellin
import OAI.NumberTheory.CubicMoment.Estimates.ThetaUpperVerticalBound

namespace OAI

/-! The actual angular completion is uniformly bounded on every closed vertical strip. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaLevelAngularCompleted_bounded_strip {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (rev : Bool) (k : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖cubicThetaLevelAngularCompleted q x y rev k s‖≤C := by
  let f := cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
    (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q)
  let g := cubicThetaScaledAngularAxis (cubicThetaCircleOrder (!rev) k)
    (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q)
  let ε := cubicThetaLevelAngularPhase q x rev k
  let B := ((2*k:ℕ):ℝ)-a
  refine ⟨thetaUpperNormMass f b+‖ε‖*thetaUpperNormMass g B,
    add_nonneg (thetaUpperNormMass_nonneg f b)
      (mul_nonneg (_root_.norm_nonneg ε) (thetaUpperNormMass_nonneg g B)),?_⟩
  intro s hs
  have hf : ‖mellin (thetaUpper f) s‖≤thetaUpperNormMass f b :=
    thetaUpper_vertical_bound
      (cubicThetaScaledAngularUpper_mellinConvergent _ _ (cubicThetaLevelScale_pos hq) _) hs.2
  have hg : ‖mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s)‖≤thetaUpperNormMass g B := by
    apply thetaUpper_vertical_bound
      (cubicThetaScaledAngularUpper_mellinConvergent _ _ (cubicThetaLevelScale_pos hq) _)
    simp only [Complex.sub_re,Complex.natCast_re]
    exact sub_le_sub_left hs.1 _
  change ‖mellin (thetaUpper f) s+ε*mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s)‖≤_
  exact (norm_add_le _ _).trans (add_le_add hf (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hg (_root_.norm_nonneg ε)))

end CubicFirstMoment

end

end OAI
