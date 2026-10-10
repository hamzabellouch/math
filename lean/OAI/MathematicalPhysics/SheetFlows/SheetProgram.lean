import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Uniqueness
import OAI.MathematicalPhysics.SheetFlows.EffectiveForcing

namespace OAI

/-! SheetFlows sheet program. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem sheet_theorem {N : ℕ} (D : SheetData N) (ν : ℝ)
    (hν : 0 < ν) (hνcomp : ComputableReal ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧
      (N = 0 → f = 0 ∧ u = 0) := by
  cases N with
  | zero => exact sheet_theorem_empty D ν hν
  | succ N =>
      obtain ⟨δ,hδ,hδsmall,hs,ht⟩ := D.exists_rational_collar
      have hδsmall' : (δ:ℝ) ≤ 1/10 := by
        have hc : δ*10 ≤ 1 := (le_div_iff₀ (by norm_num)).mp hδsmall
        have hc' : (δ:ℝ)*10 ≤ 1 := by exact_mod_cast hc
        linarith
      let d : Collar := ⟨(δ:ℝ), by exact_mod_cast hδ, hδsmall'⟩
      let P := sheetProgram d D
      let v : Fin P.length → Space → Space := fun i => (P.get i).field
      obtain ⟨hfsp,husp,hfs,hus,hfm,_,hfd,_,hfp,hup,hsol,hcol,hadv,_,_⟩ :=
        scheduled_direct_forcing v (fun i => (P.get i).smooth)
          (fun i => (P.get i).periodic) (fun i => (P.get i).mean_zero)
          (fun i => (P.get i).divergence_zero) (fun i => (P.get i).nonlinear_zero) ν
      have hformula : HasRationalFormula (scheduleVelocity v) :=
        sheetVelocity_formula d ⟨δ,rfl⟩ D
      obtain ⟨heff,hbounds⟩ := hformula.directForce_effective hus husp hup hνcomp
      obtain ⟨hflow,hend⟩ := schedule_material_flow v (fun i => (P.get i).straight)
      refine ⟨globalDirectForce ν (scheduleVelocity v), scheduleVelocity v,
        fun t a => repeatedPath v a t, hfsp,husp,hfs,hus,heff,hfm,hfd,hfp,hsol,
        ?_,hflow,?_,hcol,hadv,hbounds,hformula.circuit.effectiveBounds hus husp hup,?_⟩
      · intro w p hw t ht x
        exact hsol.unique hw hν.le ht x
      · intro i y hy
        dsimp only
        rw [hend,stageState_list_eq P, sheetProgram_on d D hs ht i hy]
      · simp

end Solenoidal
end
end


end OAI
