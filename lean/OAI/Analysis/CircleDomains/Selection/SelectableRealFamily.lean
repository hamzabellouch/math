import OAI.Analysis.CircleDomains.Rigidity.SelectableMaskedCoordinate
import OAI.Analysis.CircleDomains.Selection.RealCoordinateData
import OAI.Analysis.CircleDomains.Selection.RealCoordinateFamily
import OAI.Analysis.CircleDomains.Selection.ZeroRealCoordinate
import OAI.Analysis.CircleDomains.Rigidity.OrderedMaskedSelection

namespace OAI

/-! The already selected real barriers become the seed of mixed selection.
All their physical functions and band endpoints are kept, while the temporary
label set is the entire dust. Compatibility is kept on the original free set. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selectable_real_family
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust) (EStar : Set Sphere)
    (c : ℕ → UngatedRealTest d π EStar)
    (hc0 : (c 0).coordinate.quotient = fun _ => 0)
    (M : Set Sphere) (hM : M.Countable) (hMB : M ⊆ d.dust)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M)) :
    ∃ seed : ℕ → SelectableMaskedCoordinate d π,
      (∀ i, M ⊆ (seed i).flags) ∧
      (∀ i, (seed i).coordinate.graph = circleBandGraph d.quotientDomain (c i).coordinate.quotient) ∧
      (∀ i x, (seed i).coordinate.physical x = ((c i).coordinate.physical x : UnitAddCircle)) ∧
      (∀ i s, (seed i).coordinate.lower s = liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] s.val) ∧
        (seed i).coordinate.upper s = limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] s.val)) ∧
      (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0) ∧
      (∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
            (fun k => (seed k).coordinate.graph) labels) = 0) ∧
      Nonempty (RealCoordinateSubfamily (fun i => (seed i).coordinate) id) := by
  have hempty (j n : ℕ) (labels : Fin n → ℕ) (_ : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ d.dust)
          (circleBandGraph d.quotientDomain (c j).coordinate.quotient)
          (fun k => circleBandGraph d.quotientDomain (c k).coordinate.quotient) labels) = 0 := by
    simp [freeComponentFailure]
  let F := realCoordinateFamily d hU hdense π he hB (fun i => (c i).coordinate)
    d.dust (Subset.refl _) (fun i => (c i).weight) (fun i => (c i).weight_finite)
    (fun _ _ hx _ => hx) (fun i => (c i).band_bound) hempty
  let C (i : ℕ) : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val) := F.maskedCoordinate hG p i
  have hex (i : ℕ) : ∃ q : SelectableMaskedCoordinate d π,
      q.coordinate = C i ∧ M ⊆ q.flags :=
    SelectableMaskedCoordinate.exists_of_real hcoarea d hU hG π he (c i).coordinate
      (C i) rfl M hM hMB
  let seed (i : ℕ) := (hex i).choose
  have hC (i : ℕ) : (seed i).coordinate = C i := (hex i).choose_spec.1
  have hmark (i : ℕ) : M ⊆ (seed i).flags := (hex i).choose_spec.2
  have hgraph (i : ℕ) : (seed i).coordinate.graph =
      circleBandGraph d.quotientDomain (c i).coordinate.quotient := by rw [hC]; rfl
  refine ⟨seed, hmark, hgraph, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    rw [hC]
    rfl
  · intro i s
    rw [hC]
    exact ⟨rfl, rfl⟩
  · rw [hgraph, hc0]
  · intro j n labels hlt
    have hz := hcompat j n labels hlt
    have hrel : levelRelation (realTestLevelData d c).levels =
        fun i => (seed i).coordinate.graph := by
      funext i
      rw [realTestLevelData.level_relation, hgraph]
    rw [hrel] at hz
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ labels) hz
    intro x hx
    exact ⟨hx.1, fun hm => hx.2 (mem_iUnion.mpr ⟨0, hmark 0 hm⟩)⟩
  · have heq : (fun i => (seed i).coordinate) = C := funext hC
    rw [heq]
    exact ⟨F.realSubfamily hG p⟩

end CircleDomainRigidity

end

end OAI
