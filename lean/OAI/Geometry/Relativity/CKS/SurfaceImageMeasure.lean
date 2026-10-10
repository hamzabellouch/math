import OAI.Geometry.Relativity.CKS.InducedSphereCalculus

namespace OAI

noncomputable section
open Set MeasureTheory Manifold
namespace CKSSurfaceVolume
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma sigmaCompact_open [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  simpa using IsSigmaCompact.image (f := (Subtype.val : U → X)) continuous_subtype_val isSigmaCompact_univ

lemma sigmaCompact_inter_closed {s t : Set X} (hs : IsSigmaCompact s) (ht : IsClosed t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K,hK,hcov⟩ := hs
  refine ⟨fun n => K n ∩ t,fun n => (hK n).inter_right ht,?_⟩
  rw [← iUnion_inter,hcov]

lemma sigmaCompact_measurable [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : IsSigmaCompact s) : MeasurableSet s := by
  obtain ⟨K,hK,rfl⟩ := hs
  exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)

lemma sigmaCompact_disjointed_open [LocallyCompactSpace X] [SecondCountableTopology X]
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) (n : ℕ) : IsSigmaCompact (disjointed U n) := by
  rw [disjointed_eq_inter_compl]
  exact sigmaCompact_inter_closed (sigmaCompact_open (hU n)) (isClosed_iInter (fun j => isClosed_iInter (fun _ => (hU j).isClosed_compl)))

end CKSSurfaceVolume

end

end OAI
