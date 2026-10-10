import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileEnergyDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingContinuousRealization
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.WeightedEnergyEstimate

namespace OAI

/-! # The actual torus propagator obeys the compact-observation energy estimate -/

open Set

namespace DefocusingNLS

theorem expandingProfileTrajectory_observation_estimate (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q)
    (q : C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ s, ‖q s‖ ≤ Q)
    (c C R : ℝ)
    (henergy : ∀ (s : Icc (0 : ℝ) T) (v : FourierL2),
      let l := expandingRadiusCurve L T hL s;
      -a * ‖expandingLowEnergy a k l.1 l.2 v‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k l.1 l.2 v‖ ^ 2 +
        2 * inner ℝ v (expandingLinearizedPotential a k l.1 ha ha1 hk l.2 m (q s) v) ≤
      -c * ‖v‖ ^ 2 + C * ‖expandingPhysicalBall a k l.1 R ha ha1 hk l.2 v‖ ^ 2)
    (f : FourierL2) (t : Icc (0 : ℝ) T) :
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f
    let l := expandingRadiusCurve L T hL
    ‖S t‖ ^ 2 ≤ Real.exp (-c * t) * ‖f‖ ^ 2 +
      ∫ τ in (0 : ℝ)..(t : ℝ),
        (let s := projIcc 0 T hT τ;
        Real.exp (-c * ((t : ℝ) - τ)) *
          (C * ‖expandingPhysicalBall a k (l s).1 R ha ha1 hk (l s).2 (S s)‖ ^ 2)) := by
  intro S l
  let p := fun τ => projIcc 0 T hT τ
  let F := fun τ => ‖S (p τ)‖ ^ 2
  let r := expandingReactionHistory T hT (expandingProfileReaction a k T ha ha1 hk m l q 0) S
  let D := fun τ =>
    -a * ‖expandingLowEnergy a k (l (p τ)).1 (l (p τ)).2 (S (p τ))‖ ^ 2 +
      (6 - 2 * a - k) * ‖expandingHighEnergy a k (l (p τ)).1 (l (p τ)).2 (S (p τ))‖ ^ 2 +
      2 * inner ℝ (S (p τ)) (r τ)
  let H := fun τ => C * ‖expandingPhysicalBall a k (l (p τ)).1 R ha ha1 hk (l (p τ)).2 (S (p τ))‖ ^ 2
  have hF : Continuous F := (S.continuous.comp continuous_projIcc).norm.pow 2
  have hr : Continuous r := continuous_expandingReactionHistory T hT _ S
  have hforce (τ : ℝ) : r τ =
      expandingLinearizedPotential a k (l (p τ)).1 ha ha1 hk (l (p τ)).2 m (q (p τ)) (S (p τ)) := by
    change (-Complex.I) • _ + (0 : FourierL2) = _
    exact add_zero _
  have hD : Continuous D :=
    ((continuous_const.mul ((continuous_expandingLowEnergy_sq a b k L T ha hk hL S).comp
      continuous_projIcc)).add
      (continuous_const.mul ((continuous_expandingHighEnergy_sq a b k L T ha hk hL S).comp
        continuous_projIcc))).add
        (continuous_const.mul ((S.continuous.comp continuous_projIcc).inner hr))
  have hH : Continuous H := continuous_const.mul
    (((continuous_expandingPhysicalBall a k R ha ha1 hk).comp
      ((l.continuous.comp continuous_projIcc).prodMk
        (S.continuous.comp continuous_projIcc))).norm.pow 2)
  have hd (τ : ℝ) (hτ : τ ∈ Ioo 0 (t : ℝ)) : HasDerivAt F (D τ) τ :=
    hasDerivAt_expandingMildEnergy a b k L T ha hk hL hT S r hr f
      (fun s => expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m Q hQ q hq f s)
      τ ⟨hτ.1, hτ.2.trans_le t.2.2⟩
  have hb (τ : ℝ) (_hτ : τ ∈ Icc 0 (t : ℝ)) : D τ ≤ -c * F τ + H τ := by
    dsimp only [D]
    rw [hforce]
    exact henergy (p τ) (S (p τ))
  have h := energy_decay_estimate F D H c t t.2.1 hF hD hH hd hb
  have hpt : p t = t := projIcc_of_mem hT t.2
  have hp0 : p 0 = ⟨0, le_rfl, hT⟩ := projIcc_of_mem hT ⟨le_rfl, hT⟩
  have hS0 : S ⟨0, le_rfl, hT⟩ = f := by
    have he := expandingProfileTrajectory_eq a b k L T ha ha1 hk hL hT m Q hQ q hq f ⟨0, le_rfl, hT⟩
    simpa [expandingFreeStep_zero, expandingDuhamel] using he
  simpa only [F, H, hpt, hp0, hS0] using h

end DefocusingNLS

end OAI
