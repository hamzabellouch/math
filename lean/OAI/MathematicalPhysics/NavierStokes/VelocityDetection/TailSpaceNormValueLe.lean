import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceContDiffPartialDInfty

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open SpatialCalculus HeatKernels

theorem norm_value_le {n a : ℕ} (J : compatibleJets n a) (X : Coord n) :
    ‖value J X‖ ≤ ‖J‖ :=
  (norm_compatible_apply_le (entry J 0 (by omega) Fin.elim0) X).trans
    (norm_entry_le J 0 (by omega) Fin.elim0)

theorem hasDerivAt_of_values {n a : ℕ} {F dF : ℝ → compatibleJets n a}
    (hdF : Continuous dF)
    (hder : ∀ t X, HasDerivAt (fun s => value (F s) X) (value (dF t) X) t) (t : ℝ) :
    HasDerivAt F (dF t) t := by
  have heq (s : ℝ) : F s = F 0 + ∫ r in (0 : ℝ)..s, dF r := by
    apply value_injective
    ext X
    change value (F s) X = evaluate X (F 0 + ∫ r in (0 : ℝ)..s, dF r)
    rw [map_add, ← (evaluate X).intervalIntegral_comp_comm (hdF.intervalIntegrable 0 s)]
    have hc : Continuous (fun r => value (dF r) X) := (evaluate X).continuous.comp hdF
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ uIcc (0 : ℝ) s) => hder r X) (hc.intervalIntegrable 0 s)
    simp only [evaluate_apply]
    rw [hh]
    ring
  let := secondCountableTopologyEither_of_left ℝ (compatibleJets n a)
  have hm : StronglyMeasurable dF := Continuous.stronglyMeasurable hdF
  have H := (intervalIntegral.integral_hasDerivAt_right (E := compatibleJets n a)
      (hdF.intervalIntegrable 0 t) hm.stronglyMeasurableAtFilter hdF.continuousAt).const_add (F 0)
  exact H.congr_of_eventuallyEq (Eventually.of_forall heq)

def directional {n a : ℕ} (v : Coord n) (J : compatibleJets n (a + 1)) :
    compatibleJets n a := ∑ i : Fin n, v i • differentiate i J

theorem value_directional {n a : ℕ} (v : Coord n) (J : compatibleJets n (a + 1))
    (X : Coord n) : value (directional v J) X = firstGradient (fun i => differentiate i J) X v := by
  change evaluate X (∑ i, v i • differentiate i J) = _
  simp only [map_sum, map_smul, evaluate_apply, firstGradient, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem norm_directional_le {n a : ℕ} (v : Coord n) (J : compatibleJets n (a + 1)) :
    ‖directional v J‖ ≤ (∑ i : Fin n, ‖v i‖) * ‖J‖ := by
  calc
    ‖directional v J‖ ≤ ∑ i : Fin n, ‖v i • differentiate i J‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖v i‖ * ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_differentiate_le i J) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem continuous_directional {n a : ℕ} (J : compatibleJets n (a + 1)) :
    Continuous (fun v : Coord n => directional v J) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).smul continuous_const

theorem hasDerivAt_translate {n a : ℕ} (J : compatibleJets n (a + 1)) (v : Coord n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => translate (r • v) (restrict (Nat.le_succ a) J))
      (translate (s • v) (directional v J)) s := by
  apply hasDerivAt_of_values
    ((continuous_translate (directional v J)).comp (continuous_id.smul continuous_const))
  intro t X
  change HasDerivAt (fun r => value J (X + r • v))
    (value (directional v J) (X + t • v)) t
  rw [value_directional]
  have hh := (hasFDerivAt_value J (X + t • v)).comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add X)
  simpa only [one_smul, comp_def, id_eq] using hh

theorem partialD_scaled_value {a : ℕ} (J : compatibleJets 2 (a + 1))
    (X : Coord 2) (s : ℝ) (i : Fin 2) (Y : Coord 2) :
    partialD i (fun Z => value J (X + s • Z)) Y =
      s * value (differentiate i J) (X + s • Y) := by
  have hh (Z : Coord 2) := (hasFDerivAt_value J (X + s • Z)).comp Z
    (((hasFDerivAt_id Z).const_smul s).const_add X)
  simp only [Pi.smul_apply, comp_def, id_eq] at hh
  rw [partialD_eq_fderiv i (fun Z => (hh Z).differentiableAt), (hh Y).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, firstGradient, sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp [Pi.single_apply]

end VelocityDetection.TailSpace.Jets
end

end OAI
