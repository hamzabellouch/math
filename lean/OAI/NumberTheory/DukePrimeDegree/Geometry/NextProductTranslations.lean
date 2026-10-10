import OAI.NumberTheory.DukePrimeDegree.Geometry.NextProductChain

namespace OAI

/-! # Translated intrinsic products in the extended-prefix time coordinates -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

lemma nextGroupCast_mul (q : InitialRootStep n)
    (w v : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    q.nextGroupCast (w*v) = q.nextGroupCast w * q.nextGroupCast v :=
  Subtype.ext rfl

end InitialRootStep
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

lemma translated_nextProduct_time_coordinates
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    ((ν.map q.nextGroupCast).map (Homeomorph.mulLeft (q.nextGroupCast w))).map
      (c.remainingWordHomeomorph q.next_initial hf).symm =
      (ν.map (Homeomorph.mulLeft w)).map (nextTimeCoordinates q c hf) := by
  rw [Measure.map_map (c.remainingWordHomeomorph q.next_initial hf).symm.measurable
      (Homeomorph.mulLeft (q.nextGroupCast w)).measurable,
    Measure.map_map
      ((c.remainingWordHomeomorph q.next_initial hf).symm.measurable.comp
        (Homeomorph.mulLeft (q.nextGroupCast w)).measurable) q.nextGroupCast.measurable,
    Measure.map_map (nextTimeCoordinates q c hf).measurable (Homeomorph.mulLeft w).measurable]
  apply congrArg (fun f => ν.map f)
  funext v
  change (c.remainingWordHomeomorph q.next_initial hf).symm
      (q.nextGroupCast w * q.nextGroupCast v) =
    (c.remainingWordHomeomorph q.next_initial hf).symm (q.nextGroupCast (w*v))
  rw [q.nextGroupCast_mul]

lemma normalized_nextProduct_time_coordinates
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hV : MeasurableSet V) :
    ((anchorNormalize ν V).restrict V).map (nextTimeCoordinates q c hf) =
      (anchorNormalize (ν.map (nextTimeCoordinates q c hf))
        (nextTimeCoordinates q c hf '' V)).restrict (nextTimeCoordinates q c hf '' V) := by
  let E := (nextTimeCoordinates q c hf).toMeasurableEquiv
  have hEV : MeasurableSet (E '' V) := E.measurableEmbedding.measurableSet_image.mpr hV
  have hn := anchorNormalize_map_equiv ν E V
  change ((anchorNormalize ν V).restrict V).map E =
    (anchorNormalize (ν.map E) (E '' V)).restrict (E '' V)
  rw [hn,Measure.restrict_map E.measurable hEV,E.injective.preimage_image]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
