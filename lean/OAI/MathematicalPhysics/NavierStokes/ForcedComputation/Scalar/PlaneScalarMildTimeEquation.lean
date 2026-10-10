import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatDuhamelEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildSourceRegularity

namespace OAI

/-! The actual time equation of the compatible scalar mild solution. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild.CompatibleData
open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

def initialValue {T : ℝ} (D : CompatibleData T) : Plane → ℝ :=
  BoundedSpatialJets.function Plane ℝ 0 (D.initial 0)

theorem initialValue_eq {T : ℝ} (D : CompatibleData T) (k : ℕ) :
    D.initialValue = (BoundedSpatialJets.function Plane ℝ k (D.initial k) : Plane → ℝ) := by
  funext x
  have he := congrArg (fun J : Jet 0 => BoundedSpatialJets.function Plane ℝ 0 J x)
    (D.initial_truncate 0 k (Nat.zero_le k))
  change BoundedSpatialJets.function Plane ℝ 0
    (BoundedSpatialJets.truncate Plane ℝ 0 k (Nat.zero_le k) (D.initial k)) x = D.initialValue x at he
  rw [BoundedSpatialJets.function_truncate] at he
  exact he.symm

theorem initialValue_smooth {T : ℝ} (D : CompatibleData T) : ContDiff ℝ ∞ D.initialValue := by
  apply contDiff_infty.mpr
  intro k
  rw [D.initialValue_eq k]
  exact BoundedSpatialJets.function_contDiff Plane ℝ k _

def solutionValue {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T)
    (t : ℝ) (x : Plane) : ℝ := D.solution hT hν (projIcc 0 T hT t) x

theorem solutionValue_heat_form {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Plane) :
    D.solutionValue hT hν t x = PlaneHeat.evolution ℝ D.initialValue (ν*t) x +
      heatSourceValue hT hν 3 (D.effectiveSource hT hν 3) t x := by
  let t' : Icc (0 : ℝ) T := ⟨t, ht⟩
  have hs := congrArg (fun u : WeaklySingular.Path (Jet 3) T => u t')
    (D.solutionJet_heat_form hT hν 3)
  change D.solutionJet hT hν 3 t' = initialHeatPath hν 3 (D.initial 4) t' +
    heatSourcePath hT hν 3 (D.effectiveSource hT hν 3) t' at hs
  have he : (BoundedSpatialJets.function Plane ℝ 3
      (BoundedSpatialJets.truncate Plane ℝ 3 4 (by omega) (D.initial 4)) : Plane → ℝ) =
        D.initialValue := by
    funext y
    rw [BoundedSpatialJets.function_truncate, D.initialValue_eq 4]
  change D.solution hT hν (projIcc 0 T hT t) x = _
  rw [projIcc_of_mem hT ht, ← D.solutionJet_function hT hν 3]
  rw [hs, BoundedSpatialJets.function_add, initialHeatPath_apply, PlaneHeat.evolutionOperator_function, he]
  simp only [heatSourceValue, sourceValue, WeaklySingular.extendPath,
    projIcc_of_mem hT ht, t']

theorem sourceValue_effectiveSource {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (s : ℝ) :
    sourceValue hT k (D.effectiveSource hT hν k) s =
      D.effectiveSourceValue hT hν (projIcc 0 T hT s) := by
  funext x
  exact (D.effectiveSourceValue_eq hT hν k (projIcc 0 T hT s) x).symm

theorem solutionValue_interior_equation {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Plane) :
    HasDerivAt (fun s => D.solutionValue hT hν s x)
      (ν * ∑ j : Fin 2, PlaneHeat.spatialPartial ℝ j
        (PlaneHeat.spatialPartial ℝ j (D.solutionValue hT hν t)) x +
          D.effectiveSourceValue hT hν (projIcc 0 T hT t) x) t := by
  have hq (s : ℝ) : ContDiff ℝ ∞ (sourceValue hT 3 (D.effectiveSource hT hν 3) s) := by
    rw [D.sourceValue_effectiveSource hT hν]
    exact D.effectiveSource_smooth hT hν _
  have hd := PlaneHeat.hasDerivAt_duhamel hT hν D.initialValue D.initialValue_smooth
    (D.initial 3) (D.initialValue_eq 3).symm (D.effectiveSource hT hν 3) hq ht x
  have he : D.solutionValue hT hν t = (fun y =>
      PlaneHeat.evolution ℝ D.initialValue (ν*t) y +
        heatSourceValue hT hν 3 (D.effectiveSource hT hν 3) t y) := by
    funext y
    exact D.solutionValue_heat_form hT hν ⟨ht.1.le, ht.2.le⟩ y
  rw [D.sourceValue_effectiveSource hT hν, ← he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact D.solutionValue_heat_form hT hν ⟨hs.1.le, hs.2.le⟩ x

end ForcedComputation.PlaneScalarMild.CompatibleData

end

end OAI
