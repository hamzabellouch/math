import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingForceEvaluation

namespace OAI

/-! Terminating rational bounds for the force on any supplied space-time box.
Only the initial viscosity approximation and a finite instruction prefix enter. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Filter
open scoped Topology

def residualBoxBound (c : NonperiodicVector) (α : List (Fin 4))
    (a : ℕ → ℚ) (R : ℚ) : ℚ :=
  (NonperiodicResidual.code c (a 0)).bound α R + NonperiodicResidual.laplaceBound c α R

theorem residualBoxBound_spec (c : NonperiodicVector) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν) (R : ℚ)
    (y : SpaceTime) (hy : ∀ j, |timeSpaceCoord j y| ≤ |(R : ℝ)|) :
    ‖mixedDerivative (residual ν c.val) α y‖ ≤ (residualBoxBound c α a R : ℝ) := by
  have hν : |ν - (a 0 : ℝ)| ≤ 1 := by
    simpa only [errorTolerance, pow_zero, inv_one] using ha 0
  have hd := NonperiodicResidual.coefficient_error c α R y hy ν (a 0)
  have hb : ‖mixedDerivative (residual (a 0) c.val) α y‖ ≤
      ((NonperiodicResidual.code c (a 0)).bound α R : ℝ) := by
    simpa only [NonperiodicResidual.val] using
      (NonperiodicResidual.code c (a 0)).val_bound α R y hy
  have he : ‖mixedDerivative (residual ν c.val) α y -
      mixedDerivative (residual (a 0) c.val) α y‖ ≤
      (NonperiodicResidual.laplaceBound c α R : ℝ) :=
    hd.trans ((mul_le_mul_of_nonneg_right hν
      (Rat.cast_nonneg.mpr (NonperiodicResidual.laplaceBound_nonneg c α R))).trans_eq
        (one_mul _))
  calc
    _ ≤ ‖mixedDerivative (residual ν c.val) α y -
        mixedDerivative (residual (a 0) c.val) α y‖ +
        ‖mixedDerivative (residual (a 0) c.val) α y‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (mixedDerivative (residual ν c.val) α y - mixedDerivative (residual (a 0) c.val) α y)
        (mixedDerivative (residual (a 0) c.val) α y)
    _ ≤ _ := by
      simpa only [residualBoxBound, Rat.cast_add, add_comm] using add_le_add he hb

def expandingForceBoxBound (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) (σ D K : ℚ)
    (p : Fin 2 → ℚ) (α : List (Fin 4)) (a : ℕ → ℚ) (R : ℚ) : ℚ :=
  residualBoxBound (prefixCode M hM blank m σ D K (expandingPrefixLength |R|)) α a R +
    (verticalSourceCode p).bound α R

theorem expandingForceBoxBound_spec (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℚ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (p : Fin 2 → ℚ) (α : List (Fin 4)) {ν : ℝ} {a : ℕ → ℚ}
    (ha : IsFastRealName a ν) (R : ℚ) (y : SpaceTime)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(R : ℝ)|) :
    ‖mixedDerivative (triangularForce ν (expandingDrift M hM blank m σ D K)
        (unitImpulse (fun j => (p j : ℝ)))) α y‖ ≤
      (expandingForceBoxBound M hM blank m σ D K p α a R : ℝ) := by
  let c := prefixCode M hM blank m σ D K (expandingPrefixLength |R|)
  have ht : y.1 ≤ |(R : ℝ)| := (le_abs_self _).trans (hy 0)
  have hN : y.1 + 2 ≤ (expandingPrefixLength |R| : ℝ) := by
    have hc : |(R : ℝ)| + 3 ≤ (expandingPrefixLength |R| : ℝ) := by
      exact_mod_cast (Nat.le_ceil (|R| + 3))
    linarith
  have hg := prefixCode_germ M hM blank m hσ hD hK _ y hN
  have hs : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hk : (0 : ℝ) ≤ K := by exact_mod_cast hK
  have hsource : (verticalSourceCode p).val =
      triangularVelocity (fun _ _ => 0) (unitImpulse (fun j => (p j : ℝ))) := by
    funext z
    rw [verticalSourceCode_val]
    simp only [triangularVelocity, triangularLift, map_zero, zero_add]
  rw [triangularForce_eq_residual (expandingDrift_smooth M hM blank m hs hd hk),
    ← hsource, mixedDerivative_add
      (residual_smooth (triangularVelocity_smooth
        (expandingDrift_smooth M hM blank m hs hd hk) contDiff_const) ν)
      (verticalSourceCode p).smooth]
  change ‖mixedDerivative (residual ν (triangularVelocity
      (expandingDrift M hM blank m σ D K) (fun _ _ => 0))) α y +
      mixedDerivative (verticalSourceCode p).val α y‖ ≤ _
  rw [(mixedDerivative_eventuallyEq (residual_eventuallyEq hg ν) α).self_of_nhds]
  exact (norm_add_le _ _).trans (by
    simpa only [expandingForceBoxBound, Rat.cast_add] using
      add_le_add (residualBoxBound_spec c α ha R y hy)
        ((verticalSourceCode p).val_bound α R y hy))

end ForcedComputation.ExpandingDetector

end

end OAI
