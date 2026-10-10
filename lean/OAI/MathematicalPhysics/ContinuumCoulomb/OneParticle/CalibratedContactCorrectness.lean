import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CalibratedContactProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactPositionArray
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactCalibratedGeometry

namespace OAI

/-! The composed numerical program outputs the actual rational geometric
realization of the final mediator graph, in its original vertex order. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedContactProgram
open ContactMediator

def graphInput (d : SquareLatticeHeisenberg) (N P H : ℕ)
    (K : GlobalEdge d → ℚ) : Input :=
  (H, ((N, P), (List.ofFn d.coordinate, (d.bonds.toList, List.ofFn K))))

def graphLengths (rho : ℕ) (ε c : ℚ) (k A B N P : ℕ)
    (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) : GlobalEdge d → ℚ :=
  fun a => AutomaticCalibration.normalizedValue rho ε c k A B (N, (P, K a))

theorem raw_graphInput (rho : ℕ) (ε c : ℚ) (k A B N P H : ℕ)
    (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) :
    rawInput rho ε c k A B (graphInput d N P H K) =
      ContactSourceInputProgram.literalInput d H (graphLengths rho ε c k A B N P d K) := by
  simp only [rawInput, graphInput, AutomaticCalibrationList.value, List.map_ofFn,
    ContactSourceInputProgram.literalInput, Function.comp_def]
  rfl

theorem value_graphInput (rho : ℕ) (ε c : ℚ) (k A B N P H : ℕ)
    (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) :
    value rho ε c k A B (graphInput d N P H K) =
      List.ofFn (fun x => ContactCalibratedGeometry.position d H
        (AutomaticCalibration.spacing c k N) (graphLengths rho ε c k A B N P d K) x) := by
  unfold value
  rw [raw_graphInput]
  exact ContactSourceInputProgram.scaled_literal_array d H
    (AutomaticCalibration.spacing c k N) (graphLengths rho ε c k A B N P d K)

theorem graphLengths_scale (rho : ℕ) (ε : ℚ) {c : ℚ} (hc : 0 < c)
    (k A B N P : ℕ) (hN : 0 < N) (d : SquareLatticeHeisenberg)
    (K : GlobalEdge d → ℚ) (a : GlobalEdge d) :
    (AutomaticCalibration.spacing c k N : ℝ) * graphLengths rho ε c k A B N P d K a =
      (AutomaticCalibration.value rho ε c k A B (N, (P, K a)) : ℝ) := by
  have hq := AutomaticCalibration.spacing_positive hc k N hN
  have heq : AutomaticCalibration.spacing c k N *
      graphLengths rho ε c k A B N P d K a =
        AutomaticCalibration.value rho ε c k A B (N, (P, K a)) := by
    unfold graphLengths AutomaticCalibration.normalizedValue
    field_simp [hq.ne']
  exact_mod_cast heq

theorem graphLengths_near_one (rho : ℕ) {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 < c)
    (hεtol : (ε : ℝ) / 2 ≤ contactLengthTolerance) (k A B N P : ℕ)
    (hN : 0 < N) (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ) (a : GlobalEdge d) :
    (graphLengths rho ε c k A B N P d K a : ℝ) ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
  obtain ⟨hl, hu⟩ := AutomaticCalibration.normalizedValue_mem rho hε hc k A B
    (N, (P, K a)) hN
  have hl' : (1 : ℝ) - (ε : ℝ) / 2 ≤ graphLengths rho ε c k A B N P d K a := by
    exact_mod_cast hl
  have hu' : (graphLengths rho ε c k A B N P d K a : ℝ) ≤ 1 + (ε : ℝ) / 2 := by
    exact_mod_cast hu
  constructor <;> linarith

theorem graph_separation (rho : ℕ) {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 < c)
    (hεtol : (ε : ℝ) / 2 ≤ contactLengthTolerance) (k A B N P H W G : ℕ)
    (hN : 0 < N) (hH : 7200 ≤ H) (d : SquareLatticeHeisenberg) (K : GlobalEdge d → ℚ)
    (x y : GlobalSite d) (hxy : x ≠ y) :
    (9 / 10 : ℝ) * AutomaticCalibration.spacing c k N ≤
      dist (ContactCalibratedGeometry.point d H (AutomaticCalibration.spacing c k N)
        (graphLengths rho ε c k A B N P d K) x)
        (ContactCalibratedGeometry.point d H (AutomaticCalibration.spacing c k N)
          (graphLengths rho ε c k A B N P d K) y) :=
  ContactCalibratedGeometry.separation d W G H (AutomaticCalibration.spacing_positive hc k N hN)
    _ hH (graphLengths_near_one rho hε hc hεtol k A B N P hN d K) x y hxy

end ContinuumCoulomb.CalibratedContactProgram

end

end OAI
