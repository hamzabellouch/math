import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatSourceDerivative
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatAppliedContinuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetLinear

namespace OAI

/-! Continuous bounded source jets supply all hypotheses for Gaussian source differentiation. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open ShearFlows Set Filter MeasureTheory
open scoped Topology NNReal ContDiff Interval BigOperators

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasDerivAt_heat_source_of_jets {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (g : ℝ → Plane → F) (hg : ∀ s, ContDiff ℝ ∞ (g s))
    (J : C(ℝ, BoundedSpatialJets.Space Plane F 3))
    (hJ : ∀ s x, BoundedSpatialJets.function Plane F 3 (J s) x = g s x)
    (B : ℝ) (hB : ∀ s, ‖J s‖ ≤ B) (x : Plane) :
    HasDerivAt (fun u => ∫ s in 0..u, evolution F (g s) (ν*(u-s)) x)
      ((∫ s in 0..t, ν • ∑ j : Fin 2,
        evolution F (spatialPartial F j (spatialPartial F j (g s))) (ν*(t-s)) x) + g t x) t := by
  let P := BoundedSpatialJets.truncateCLM Plane F 1 3 (by omega)
  let Q (j : Fin 2) := BoundedSpatialJets.directionalDerivativeCLM Plane F 2 (Pi.single j 1)
  let R (j : Fin 2) := BoundedSpatialJets.directionalDerivativeCLM Plane F 1 (Pi.single j 1)
  have hfun (s : ℝ) : (BoundedSpatialJets.function Plane F 3 (J s) : Plane → F) = g s := by
    funext y
    exact hJ s y
  have hfirst (s : ℝ) (j : Fin 2) :
      (BoundedSpatialJets.function Plane F 2 (Q j (J s)) : Plane → F) =
        spatialPartial F j (g s) := by
    funext y
    change BoundedSpatialJets.function Plane F 2
      (BoundedSpatialJets.directionalDerivativeCLM Plane F 2 (Pi.single j 1) (J s)) y = _
    rw [BoundedSpatialJets.function_directionalDerivativeCLM, hfun]
    rfl
  have hsecond (s : ℝ) (j : Fin 2) :
      (BoundedSpatialJets.function Plane F 1 (R j (Q j (J s))) : Plane → F) =
        spatialPartial F j (spatialPartial F j (g s)) := by
    funext y
    change BoundedSpatialJets.function Plane F 1
      (BoundedSpatialJets.directionalDerivativeCLM Plane F 1 (Pi.single j 1) (Q j (J s))) y = _
    rw [BoundedSpatialJets.function_directionalDerivativeCLM, hfirst]
    rfl
  have hnormQ (j : Fin 2) : ‖Q j‖ ≤ 1 := by
    simpa only [Q, Pi.norm_single, norm_one] using
      BoundedSpatialJets.norm_directionalDerivativeCLM_le Plane F 2 (Pi.single j 1)
  have hnormR (j : Fin 2) : ‖R j‖ ≤ 1 := by
    simpa only [R, Pi.norm_single, norm_one] using
      BoundedSpatialJets.norm_directionalDerivativeCLM_le Plane F 1 (Pi.single j 1)
  have hQ (s : ℝ) (j : Fin 2) : ‖Q j (J s)‖ ≤ B :=
    ((Q j).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hnormQ j) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hB s))
  have hR (s : ℝ) (j : Fin 2) : ‖R j (Q j (J s))‖ ≤ B :=
    ((R j).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hnormR j) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hQ s j))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hC (s : ℝ) (y : Plane) : ‖g s y‖ ≤ B := by
    rw [← hJ s y]
    exact (BoundedSpatialJets.norm_function_le Plane F 3 _ y).trans (hB s)
  have hD (s : ℝ) (j : Fin 2) (y : Plane) : ‖spatialPartial F j (g s) y‖ ≤ B := by
    rw [← hfirst s j]
    exact (BoundedSpatialJets.norm_function_le Plane F 2 _ y).trans (hQ s j)
  have hE (s : ℝ) (j : Fin 2) (y : Plane) :
      ‖spatialPartial F j (spatialPartial F j (g s)) y‖ ≤ B := by
    rw [← hsecond s j]
    exact (BoundedSpatialJets.norm_function_le Plane F 1 _ y).trans (hR s j)
  have hP (s : ℝ) : (BoundedSpatialJets.function Plane F 1 (P (J s)) : Plane → F) = g s := by
    funext y
    change BoundedSpatialJets.function Plane F 1
      (BoundedSpatialJets.truncate Plane F 1 3 (by omega) (J s)) y = _
    rw [BoundedSpatialJets.function_truncate, hJ]
  have hL (s : ℝ) : LipschitzWith ⟨B, hB0⟩ (g s) := by
    have hl := (BoundedSpatialJets.valueMap Plane F).lipschitz.comp
      (jet_lipschitz F 0 (P (J s)) 0)
    have he : (fun y => BoundedSpatialJets.valueMap Plane F ((P (J s)).val 0 y)) = g s := by
      exact hP s
    simp only [one_mul] at hl
    change LipschitzWith ‖P (J s)‖₊
      (fun y => BoundedSpatialJets.valueMap Plane F ((P (J s)).val 0 y)) at hl
    rw [he] at hl
    apply hl.weaken
    change ‖P (J s)‖ ≤ B
    exact (BoundedSpatialJets.norm_truncate_le Plane F 1 3 (by omega) (J s)).trans (hB s)
  have hc : Continuous (fun p : ℝ × ℝ => evolution F (g p.2) (ν*(p.1-p.2)) x) := by
    have hm : Continuous (fun p : ℝ × ℝ => (ν*(p.1-p.2), P (J p.2))) :=
      (continuous_const.mul (continuous_fst.sub continuous_snd)).prodMk
        (P.continuous.comp (J.continuous.comp continuous_snd))
    have hh := (appliedHeat_joint_continuous F x).comp hm
    simpa only [Function.comp_def, appliedHeat_eq, hP] using hh
  have hdc : Continuous (fun s => ν • ∑ j : Fin 2,
      evolution F (spatialPartial F j (spatialPartial F j (g s))) (ν*(t-s)) x) := by
    apply Continuous.const_smul
    apply continuous_finsetSum
    intro j _
    have hm : Continuous (fun s : ℝ => (ν*(t-s), R j (Q j (J s)))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).prodMk
        ((R j).continuous.comp ((Q j).continuous.comp J.continuous))
    have hh := (appliedHeat_joint_continuous F x).comp hm
    simpa only [Function.comp_def, appliedHeat_eq, hsecond] using hh
  exact hasDerivAt_heat_source F hν ht g hg ⟨B, hB0⟩ hL B B B hC hD hE x hc hdc

end ForcedComputation.PlaneHeat

end

end OAI
