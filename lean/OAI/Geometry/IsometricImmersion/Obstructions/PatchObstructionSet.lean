import OAI.Geometry.IsometricImmersion.Immersions.BoundedHeightClasses
import Mathlib.Topology.Baire.Lemmas

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def patchObstructionSet (g0 : MetricField) (kappa : ℝ) : Set (metricPatchSet g0 kappa) :=
  ⋂ index : ℕ × ℚ, (closure (boundedHeightClass g0 kappa index.1 index.2))ᶜ

theorem patchObstructionSet_isGdelta (g0 : MetricField) (kappa : ℝ) :
    IsGδ (patchObstructionSet g0 kappa) :=
  IsGδ.iInter_of_isOpen (fun _ => isClosed_closure.isOpen_compl)

theorem mem_patchObstructionSet_iff {g0 : MetricField} {kappa : ℝ}
    {eta : metricPatchSet g0 kappa} :
    eta ∈ patchObstructionSet g0 kappa ↔
      ∀ M : ℕ, ∀ q0 : ℚ, eta ∉ closure (boundedHeightClass g0 kappa M q0) := by
  simp only [patchObstructionSet, mem_iInter, mem_compl_iff, Prod.forall]

theorem patchObstructionSet_has_no_admissible_height
    {g0 : MetricField} {kappa : ℝ} {eta : metricPatchSet g0 kappa}
    (heta : eta ∈ patchObstructionSet g0 kappa) :
    ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  intro z hz
  obtain ⟨M,hM,q0,hq0⟩ := every_admissible_height_has_class hz kappa
  have hclass : eta ∈ boundedHeightClass g0 kappa M q0 := ⟨z,hM,hq0⟩
  exact (mem_patchObstructionSet_iff.mp heta M q0) (subset_closure hclass)

theorem patchObstructionSet_subset_complement_admissible (g0 : MetricField) (kappa : ℝ) :
    patchObstructionSet g0 kappa ⊆ (admissiblePatchMetricSet g0 kappa)ᶜ := by
  intro eta heta hbad
  obtain ⟨z,hz⟩ := hbad
  exact patchObstructionSet_has_no_admissible_height heta z hz

end SmoothLocal.Perturbation

end

end OAI
