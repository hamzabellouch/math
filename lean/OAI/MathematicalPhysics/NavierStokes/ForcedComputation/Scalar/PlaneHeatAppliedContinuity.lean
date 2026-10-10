import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatTimeLipschitz

namespace OAI

/-! Joint continuity of heat evolution with a varying bounded initial jet. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open ShearFlows Set Filter
open scoped Topology NNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_evolutionOperator_apply_le (k : ℕ) (r : ℝ)
    (J : BoundedSpatialJets.Space Plane F k) : ‖evolutionOperator F k r J‖ ≤ ‖J‖ := by
  by_cases hr : 0 < r
  · rw [evolutionOperator, dite_eq_left hr]
    exact norm_heatOperator_apply_le F k r hr J
  · simp only [evolutionOperator, dite_eq_right hr, ContinuousLinearMap.id_apply, le_refl]

def appliedHeat (r : ℝ) (x : Plane) : BoundedSpatialJets.Space Plane F 1 →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    ((BoundedSpatialJets.functionMap Plane F 0).comp
      ((evolutionOperator F 0 r).comp (BoundedSpatialJets.truncateCLM Plane F 0 1 (by omega))))

theorem appliedHeat_eq (r : ℝ) (x : Plane) (J : BoundedSpatialJets.Space Plane F 1) :
    appliedHeat F r x J = evolution F (BoundedSpatialJets.function Plane F 1 J) r x := by
  change BoundedSpatialJets.function Plane F 0
    (evolutionOperator F 0 r (BoundedSpatialJets.truncate Plane F 0 1 (by omega) J)) x = _
  rw [evolutionOperator_function]
  congr 1

theorem norm_appliedHeat_le (r : ℝ) (x : Plane) : ‖appliedHeat F r x‖ ≤ 1 := by
  apply (appliedHeat F r x).opNorm_le_bound zero_le_one
  intro J
  rw [one_mul]
  exact (BoundedSpatialJets.norm_function_le Plane F 0 _ x).trans <|
    (norm_evolutionOperator_apply_le F 0 r _).trans <|
      BoundedSpatialJets.norm_truncate_le Plane F 0 1 (by omega) J

theorem appliedHeat_time_continuous (J : BoundedSpatialJets.Space Plane F 1) (x : Plane) :
    Continuous (fun r => appliedHeat F r x J) := by
  have hL : LipschitzWith ‖J‖₊ (BoundedSpatialJets.function Plane F 1 J) := by
    have h := (BoundedSpatialJets.valueMap Plane F).lipschitz.comp
      (jet_lipschitz F 0 J 0)
    convert! h using 1
    simp only [one_mul]
  have h := evolution_time_continuous F hL ‖J‖ (BoundedSpatialJets.norm_function_le Plane F 1 J) x
  simpa only [appliedHeat_eq] using h

/-- The extra first jet supplies uniform initial continuity even when both time and
initial data vary. -/
theorem appliedHeat_joint_continuous (x : Plane) :
    Continuous (fun p : ℝ × BoundedSpatialJets.Space Plane F 1 => appliedHeat F p.1 x p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro r
    apply (appliedHeat F r x).lipschitzWith.weaken
    exact_mod_cast norm_appliedHeat_le F r x
  · intro J
    exact appliedHeat_time_continuous F J x

end ForcedComputation.PlaneHeat

end

end OAI
