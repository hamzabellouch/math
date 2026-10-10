import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileObservation

namespace OAI

/-! # An observed coefficient family controls every later expanding slab -/

open Set

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem expandingObservedFamily_energy (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q : C(Radius, FourierL2)) (Q : ℝ) (hQ : 0 ≤ Q) (hq : ∀ l, ‖q l‖ ≤ Q)
    (c C R L₀ : ℝ)
    (henergy : ∀ (l : Radius), L₀ ≤ l.1 → ∀ v : FourierL2,
      -a * ‖expandingLowEnergy a k l.1 l.2 v‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k l.1 l.2 v‖ ^ 2 +
        2 * inner ℝ v (expandingLinearizedPotential a k l.1 ha ha1 hk l.2 m (q l) v) ≤
      -c * ‖v‖ ^ 2 + C * ‖expandingPhysicalBall a k l.1 R ha ha1 hk l.2 v‖ ^ 2)
    (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T) (hLL : L₀ ≤ L)
    (f : FourierL2) (t : Icc (0 : ℝ) T) :
    let l := expandingRadiusCurve L T hL
    let p := q.comp l
    let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ p (fun s => hq (l s)) f
    ‖S t‖ ^ 2 ≤ Real.exp (-c * t) * ‖f‖ ^ 2 +
      ∫ τ in (0 : ℝ)..(t : ℝ),
        (let s := projIcc 0 T hT τ;
        Real.exp (-c * ((t : ℝ) - τ)) *
          (C * ‖expandingPhysicalBall a k (l s).1 R ha ha1 hk (l s).2 (S s)‖ ^ 2)) := by
  intro l p S
  apply expandingProfileTrajectory_observation_estimate a b k L T ha ha1 hk hL hT m Q hQ p
    (fun s => hq (l s)) c C R
  intro s v
  exact henergy (l s) (hLL.trans (expandingRadius_ge L s hL s.2.1)) v

end DefocusingNLS

end OAI
