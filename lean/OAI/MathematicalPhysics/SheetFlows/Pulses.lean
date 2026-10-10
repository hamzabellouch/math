import Mathlib
import OAI.MathematicalPhysics.SheetFlows.RectangleGeometry
import OAI.MathematicalPhysics.SheetFlows.Trajectories
import OAI.MathematicalPhysics.SheetFlows.Uniqueness

namespace OAI

/-! SheetFlows pulses. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem sheet_theorem_empty (D : SheetData 0) (ν : ℝ) (hν : 0 < ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin 0, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧ (0 = 0 → f = 0 ∧ u = 0) := by
  refine ⟨0, 0, fun _ a => a, zero_spatially_periodic, zero_spatially_periodic,
    zero_smooth, zero_smooth, zero_effective, zero_mean_zero, zero_divergence_free,
    zero_one_periodic, zero_classical_solution ν, ?_, zero_material_flow, ?_,
    zero_integer_collars, ?_, zero_effective_bounds, zero_effective_bounds, fun _ => ⟨rfl, rfl⟩⟩
  · intro v p hv t ht x
    exact (zero_classical_solution ν).unique hv hν.le ht x
  · intro i
    exact Fin.elim0 i
  · intro t x
    simp

structure StationaryPulse where
  field : Space → Space
  smooth : ContDiff ℝ (⊤ : ℕ∞) field
  periodic : ∀ x k, field (x + deck k) = field x
  mean_zero : (∫ x in fundamentalCell, field x) = 0
  divergence_zero : DivergenceFree (fun _ => field)
  nonlinear_zero : ∀ x, fderiv ℝ field x (field x) = 0
  straight : StraightInvariant field

namespace StationaryPulse

def apply (p : StationaryPulse) (a : Space) : Space := a + p.field a

def scale (c : ℝ) (p : StationaryPulse) : StationaryPulse where
  field := fun x => c • p.field x
  smooth := p.smooth.const_smul c
  periodic := by intro x k; rw [p.periodic]
  mean_zero := by rw [integral_smul, p.mean_zero, smul_zero]
  divergence_zero := by
    intro t x
    change ∑ j : Fin 3, (fderiv ℝ (fun a => c • p.field a) x (basis j)) j = 0
    simp only [fderiv_fun_const_smul (p.smooth.differentiable (by simp) x),
      smul_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have h := p.divergence_zero t x
    change (∑ j : Fin 3, (fderiv ℝ p.field x (basis j)) j) = 0 at h
    rw [h, mul_zero]
  nonlinear_zero := by
    intro x
    rw [fderiv_fun_const_smul (p.smooth.differentiable (by simp) x)]
    simp only [smul_apply, map_smul, p.nonlinear_zero, smul_zero]
  straight := by
    intro x s
    change c • p.field (x + s • (c • p.field x)) = c • p.field x
    rw [← mul_smul, p.straight]

def tensor (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j, Function.Periodic (g j) 10)
    (hi : ∀ s, g i s = 1) (j : Fin 3)
    (hz : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0) : StationaryPulse where
  field := tensorVelocity i g 0
  smooth := (tensorScalar_contDiff g hsm).smul contDiff_const
  periodic := (tensorVelocity_spatially_periodic i g hp) 0
  mean_zero := tensorVelocity_mean_zero i g j hz 0
  divergence_zero := tensorVelocity_divergence_free i g hsm hi
  nonlinear_zero := tensorVelocity_advection_zero i g hsm hi 0
  straight := by
    rw [tensorVelocity_eq_axial i g hi]
    exact axialField_straightInvariant i _

end StationaryPulse

def runProgram (P : List StationaryPulse) (a : Space) : Space :=
  P.foldl (fun x p => p.apply x) a

@[simp] theorem runProgram_nil (a : Space) : runProgram [] a = a := rfl
@[simp] theorem runProgram_cons (p : StationaryPulse) (P : List StationaryPulse) (a : Space) :
    runProgram (p :: P) a = runProgram P (p.apply a) := rfl
@[simp] theorem runProgram_append (P Q : List StationaryPulse) (a : Space) :
    runProgram (P ++ Q) a = runProgram Q (runProgram P a) := List.foldl_append

theorem runProgram_fixed (P : List StationaryPulse) (a : Space)
    (h : ∀ p ∈ P, p.field a = 0) : runProgram P a = a := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rw [runProgram_cons]
    have hp : p.apply a = a := by simp [StationaryPulse.apply, h p (by simp)]
    rw [hp]
    exact ih (fun q hq => h q (by simp [hq]))

theorem stageState_list_eq (P : List StationaryPulse) (a : Space) :
    stageState (fun i : Fin P.length => (P.get i).field) a P.length = runProgram P a := by
  have h (n : ℕ) (hn : n ≤ P.length) :
      stageState (fun i : Fin P.length => (P.get i).field) a n = runProgram (P.take n) a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn' : n < P.length := Nat.lt_of_succ_le hn
      rw [stageState, stageField_fin _ ⟨n, hn'⟩, ih (Nat.le_of_succ_le hn)]
      rw [List.take_succ_eq_append_getElem hn', runProgram_append]
      rfl
  simpa using h P.length (le_refl _)

theorem program_realization (P : List StationaryPulse) (ν : ℝ) (hν : 0 ≤ ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧ Smooth f ∧ Smooth u ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (0 : Pressure) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧ (∀ a, X 1 a = runProgram P a) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative f α z‖ ≤ B) ∧
      (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative u α z‖ ≤ B) := by
  let v : Fin P.length → Space → Space := fun i => (P.get i).field
  obtain ⟨hfsp, husp, hfs, hus, hfm, _, hfd, _, hfp, _, hsol, hcol, hadv, hfb, hub⟩ :=
    scheduled_direct_forcing v (fun i => (P.get i).smooth) (fun i => (P.get i).periodic)
      (fun i => (P.get i).mean_zero) (fun i => (P.get i).divergence_zero)
      (fun i => (P.get i).nonlinear_zero) ν
  obtain ⟨hflow, hend⟩ := schedule_material_flow v (fun i => (P.get i).straight)
  refine ⟨globalDirectForce ν (scheduleVelocity v), scheduleVelocity v,
    fun t a => repeatedPath v a t, hfsp, husp, hfs, hus, hfm, hfd, hfp, hsol,
    ?_, hflow, ?_, hcol, hadv, hfb, hub⟩
  · intro w p hw t ht x
    exact hsol.unique hw hν ht x
  · intro a
    exact (hend a).trans (stageState_list_eq P a)

end Solenoidal
end

end OAI
