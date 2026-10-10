import OAI.Analysis.CircleDomains.Topology.AssignedCollarExclusion
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

namespace OAI

/-! Fixed-circuit exclusions in the compact-open space of maps and disks.
The circuit restriction is continuous, so these are the open sets used by
countable selection, not just open sets of boundary traces. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

abbrev FiniteSource (G : Set Sphere) := {z : ℂ // (z : Sphere) ∈ G}
abbrev MapDiskData (G : Set Sphere) := C(FiniteSource G, ℂ) × (ℂ × ℝ≥0)

 theorem mapDiskData_secondCountable {G : Set Sphere} (hG : IsOpen G) :
    SecondCountableTopology (MapDiskData G) := by
  let : LocallyCompactSpace (FiniteSource G) :=
    (hG.preimage OnePoint.continuous_coe).locallyCompactSpace
  infer_instance

 def circuitRestriction {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (p : MapDiskData G) : BoundaryPairData := (p.1.comp γ, p.2)

 theorem continuous_circuitRestriction {G : Set Sphere} (γ : C(PathTime, FiniteSource G)) :
    Continuous (circuitRestriction γ) :=
  ((ContinuousMap.continuous_precomp γ).comp continuous_fst).prodMk continuous_snd

 def mapDiskExclusion {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (v : ℝ → ℝ) (budget : ℝ) : Set (MapDiskData G) :=
  circuitRestriction γ ⁻¹' boundaryExclusionSet v budget

 theorem isOpen_mapDiskExclusion {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (budget : ℝ) :
    IsOpen (mapDiskExclusion γ v budget) :=
  (isOpen_boundaryExclusionSet v hv budget).preimage (continuous_circuitRestriction γ)

 def sourceCircuit {G : Set Sphere} (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hG : ∀ t, (γ t : Sphere) ∈ G) : C(PathTime, FiniteSource G) :=
  ⟨fun t => ⟨γ t, hG t⟩, (hγ.comp continuous_subtype_val).subtype_mk _⟩

 def finiteSourceMap {G : Set Sphere} (F : ℂ → ℂ)
    (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G)) : C(FiniteSource G, ℂ) :=
  ⟨fun z => F z, hF.domRestrict⟩

 theorem circuitRestriction_source {G : Set Sphere} (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hG : ∀ t, (γ t : Sphere) ∈ G) (F : ℂ → ℂ)
    (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G)) (c : ℂ) (r : ℝ≥0) :
    circuitRestriction (sourceCircuit γ hγ hG) (finiteSourceMap F hF, c, r) =
      (boundaryCurveTrace (F ∘ γ) (hF.comp_continuous hγ hG), c, r) := rfl

end CircleDomainRigidity

end

end OAI
