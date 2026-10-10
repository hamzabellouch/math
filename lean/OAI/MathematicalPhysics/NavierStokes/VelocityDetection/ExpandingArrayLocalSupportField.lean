import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ArrayTrajectories
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CylinderDLift
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CompactTails

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open Stacks TailSpace
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

theorem localSupport_field (hν : 0 < ν) (i : Fin 2) :
    LocalHorizontalSupport (fun t X => field hb table terminal ν m t X i) := by
  intro T hT
  obtain ⟨K, hK, hzero⟩ := finiteCylinderSupport hb table terminal ν m hν T
  refine ⟨K, hK, ?_⟩
  intro t ht X hX
  by_cases ht0 : 0 ≤ t
  · exact congrFun (hzero t ht0 ((le_abs_self t).trans ht) X hX) i
  · have h := field_at_rest hb table terminal ν m hν (show t ≤ 1 by linarith) X
    exact congrFun h i

theorem field_C1Tails (hν : 0 < ν) (i : Fin 2) :
    C1Tails (fun t X => field hb table terminal ν m t X i) :=
  c1Tails_of_smooth_support ((contDiff_apply ℝ ℝ i).comp (contDiff_field hb table terminal ν m hν))
    (localSupport_field hb table terminal ν m hν i)

theorem field_D_Tails (hν : 0 < ν) (i k : Fin 2) :
    ContinuousTails (spatialD k (fun t X => field hb table terminal ν m t X i)) :=
  (spatial_c1Tails_of_smooth_support (f := fun t X => field hb table terminal ν m t X i)
    ((contDiff_apply ℝ ℝ i).comp (contDiff_field hb table terminal ν m hν))
    (localSupport_field hb table terminal ν m hν i) k).continuous

theorem field_DD_Tails (hν : 0 < ν) (i k l : Fin 2) :
    ContinuousTails (spatialD l (spatialD k (fun t X => field hb table terminal ν m t X i))) :=
  second_continuousTails_of_smooth_support (f := fun t X => field hb table terminal ν m t X i)
    ((contDiff_apply ℝ ℝ i).comp (contDiff_field hb table terminal ν m hν))
    (localSupport_field hb table terminal ν m hν i) k l

theorem comparisonClass_of_scalar_tails (hν : 0 < ν) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ ∞ (uncurry ρ)) (hr : C1Tails ρ)
    (hD : ∀ i, ContinuousTails (spatialD i ρ))
    (hDD : ∀ i k, ContinuousTails (spatialD k (spatialD i ρ))) :
    Cylinder.ComparisonClass
      (fun t x => liftVelocity (field hb table terminal ν m) ρ t (Cylinder.join x))
      (fun _ _ => 0) := by
  let v : ℝ → Coord 2 → Cylinder.Vect := fun t X =>
    ![field hb table terminal ν m t X 0, field hb table terminal ν m t X 1, ρ t X]
  have heq : (fun t x => liftVelocity (field hb table terminal ν m) ρ t (Cylinder.join x)) =
      (fun (t : ℝ) (x : Cylinder.Space) => v t x.1) := by
    funext t x
    have hh : horizontal (Cylinder.join x) = x.1 :=
      congrArg Prod.fst (Cylinder.split_join x)
    simp only [liftVelocity, hh, v]
  rw [heq]
  apply Cylinder.comparisonClass_lift_of_tails v
  · intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp (contDiff_field hb table terminal ν m hν)
    · exact (contDiff_apply ℝ ℝ (1 : Fin 2)).comp (contDiff_field hb table terminal ν m hν)
    · exact hρ
  · intro i
    fin_cases i
    · exact field_C1Tails hb table terminal ν m hν 0
    · exact field_C1Tails hb table terminal ν m hν 1
    · exact hr
  · intro i k
    fin_cases i
    · exact field_D_Tails hb table terminal ν m hν 0 k
    · exact field_D_Tails hb table terminal ν m hν 1 k
    · exact hD k
  · intro i k l
    fin_cases i
    · exact field_DD_Tails hb table terminal ν m hν 0 k l
    · exact field_DD_Tails hb table terminal ν m hν 1 k l
    · exact hDD k l

end VelocityDetection.ExpandingArray
end

end OAI
