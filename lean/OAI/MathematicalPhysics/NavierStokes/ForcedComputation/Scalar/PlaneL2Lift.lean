import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneL2Derivative

namespace OAI

/-! Canonical representatives in L2 on a finite time interval. The values
outside the specified interval have no role in the regularity statement. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set

def planeL2Lift (F : ℝ → Plane → ℝ) (S : Set ℝ)
    (hF : ∀ t ∈ S, MemLp (F t) 2 volume) (t : ℝ) : PlaneL2 := by
  classical
  exact if ht : t ∈ S then (hF t ht).toLp (F t) else 0

theorem planeL2Lift_ae (F : ℝ → Plane → ℝ) (S : Set ℝ)
    (hF : ∀ t ∈ S, MemLp (F t) 2 volume) {t : ℝ} (ht : t ∈ S) :
    (fun x => planeL2Lift F S hF t x) =ᵐ[volume] F t := by
  simp only [planeL2Lift, dite_eq_left ht]
  exact (hF t ht).coeFn_toLp

theorem exists_planeL2_continuous_representation {F : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : ∀ t ∈ S, MemLp (F t) 2 volume)
    (hc : SquareDistanceContinuousOn F S) :
    ∃ U : ℝ → PlaneL2, ContinuousOn U S ∧
      ∀ t ∈ S, (fun x => U t x) =ᵐ[volume] F t := by
  refine ⟨planeL2Lift F S hF, ?_, fun t ht => planeL2Lift_ae F S hF ht⟩
  exact planeL2_continuousOn_of_squareDistance (fun t ht => planeL2Lift_ae F S hF ht) hc

def PlaneC1L2 (F G : ℝ → Plane → ℝ) (S : Set ℝ) : Prop :=
  ∃ U V : ℝ → PlaneL2, ContinuousOn U S ∧ ContinuousOn V S ∧
    ∀ t ∈ S, ((fun x => U t x) =ᵐ[volume] F t) ∧
      ((fun x => V t x) =ᵐ[volume] G t) ∧ HasDerivWithinAt U (V t) S t

theorem planeC1L2_of_square_estimates {F G : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : ∀ t ∈ S, MemLp (F t) 2 volume)
    (hG : ∀ t ∈ S, MemLp (G t) 2 volume)
    (hcF : SquareDistanceContinuousOn F S) (hcG : SquareDistanceContinuousOn G S)
    (hd : PlaneStrongDerivativeOn F G S) : PlaneC1L2 F G S := by
  obtain ⟨U, hUc, hU⟩ := exists_planeL2_continuous_representation hF hcF
  obtain ⟨V, hVc, hV⟩ := exists_planeL2_continuous_representation hG hcG
  exact ⟨U, V, hUc, hVc, fun t ht =>
    ⟨hU t ht, hV t ht, planeL2_hasDerivWithinAt_of_strongDerivative hU hV hd ht⟩⟩

end ForcedComputation.VelocityDetector

end

end OAI
