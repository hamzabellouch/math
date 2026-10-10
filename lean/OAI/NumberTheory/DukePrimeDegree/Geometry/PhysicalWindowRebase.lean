import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixWindows
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingFactorRebase
import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteNormalizedRectangle

namespace OAI

/-! # Exact group windows after rebasing a physical rectangle -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma remainingFactor_rebase_image (d : ℕ) (q : InitialRootStep (d+1))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (t : ℝ)
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (J : Set ℝ) :
    (Homeomorph.mulLeft (q.remainingFactor (w,t))⁻¹) '' (q.remainingFactor '' (V ×ˢ J)) =
      q.remainingFactor '' ((q.nextFactorRebase d w t '' V) ×ˢ
        (Homeomorph.addRight (-t) '' J)) := by
  ext z
  constructor
  · rintro ⟨_,⟨⟨v,u⟩,⟨hv,hu⟩,rfl⟩,rfl⟩
    refine ⟨(q.nextFactorRebase d w t v,Homeomorph.addRight (-t) u),
      ⟨⟨v,hv,rfl⟩,⟨u,hu,rfl⟩⟩,?_⟩
    change q.remainingFactor (q.nextConjugation d t (w⁻¹*v),u + -t) =
      (q.remainingFactor (w,t))⁻¹*q.remainingFactor (v,u)
    simpa only [sub_eq_add_neg] using (q.remainingFactor_rebase d w v t u).symm
  · rintro ⟨⟨_,_⟩,⟨⟨v,hv,rfl⟩,⟨u,hu,rfl⟩⟩,rfl⟩
    refine ⟨q.remainingFactor (v,u),⟨(v,u),⟨hv,hu⟩,rfl⟩,?_⟩
    change (q.remainingFactor (w,t))⁻¹*q.remainingFactor (v,u) =
      q.remainingFactor (q.nextConjugation d t (w⁻¹*v),u + -t)
    simpa only [sub_eq_add_neg] using q.remainingFactor_rebase d w v t u

end InitialRootStep
namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*} [TopologicalSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}
    (B : PhysicalPrefixWindow q C g)
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

lemma group_time_image :
    (c.remainingWordHomeomorph q.initial hf) '' (B.toBox c hf).time =
      q.remainingFactor '' (B.rectangle.second ×ˢ B.interval) := by
  change (c.remainingWordHomeomorph q.initial hf) ''
    (RootPrefixCoordinates.remainingFactorTime q c hf '' (B.rectangle.second ×ˢ B.interval)) = _
  rw [image_image]
  congr 1
  funext z
  change (c.remainingWordHomeomorph q.initial hf)
    ((c.remainingWordHomeomorph q.initial hf).symm (q.remainingFactor z)) = _
  exact (c.remainingWordHomeomorph q.initial hf).apply_symm_apply _

lemma rebased_group_time_image
    (a : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :
    (Homeomorph.mulLeft
      (c.remainingWordHomeomorph q.initial hf (RootPrefixCoordinates.remainingFactorTime q c hf a))⁻¹) ''
        ((c.remainingWordHomeomorph q.initial hf) '' (B.toBox c hf).time) =
      q.remainingFactor '' ((q.nextFactorRebase d a.1 a.2 '' B.rectangle.second) ×ˢ
        (Homeomorph.addRight (-a.2) '' B.interval)) := by
  rw [B.group_time_image c hf]
  have he : c.remainingWordHomeomorph q.initial hf
      (RootPrefixCoordinates.remainingFactorTime q c hf a) = q.remainingFactor a :=
    (c.remainingWordHomeomorph q.initial hf).apply_symm_apply _
  rw [he]
  exact q.remainingFactor_rebase_image d a.1 a.2 B.rectangle.second B.interval

theorem normalized_product_on_group_time
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (η : Measure ℝ)
    [SFinite ν] [SFinite η] [IsLocallyFiniteMeasure ν]
    (a : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :
    (((anchorNormalize ν (q.nextFactorRebase d a.1 a.2 '' B.rectangle.second)).restrict
      (q.nextFactorRebase d a.1 a.2 '' B.rectangle.second)).prod
      ((anchorNormalize η (Homeomorph.addRight (-a.2) '' B.interval)).restrict
        (Homeomorph.addRight (-a.2) '' B.interval))).map q.remainingFactor =
      (anchorNormalize ((ν.prod η).map q.remainingFactor)
        ((Homeomorph.mulLeft
          (c.remainingWordHomeomorph q.initial hf
            (RootPrefixCoordinates.remainingFactorTime q c hf a))⁻¹) ''
              ((c.remainingWordHomeomorph q.initial hf) '' (B.toBox c hf).time))).restrict
        ((Homeomorph.mulLeft
          (c.remainingWordHomeomorph q.initial hf
            (RootPrefixCoordinates.remainingFactorTime q c hf a))⁻¹) ''
              ((c.remainingWordHomeomorph q.initial hf) '' (B.toBox c hf).time)) := by
  have hV : MeasurableSet (q.nextFactorRebase d a.1 a.2 '' B.rectangle.second) :=
    ((q.nextFactorRebase d a.1 a.2).isOpenMap _ B.rectangle.second_open).measurableSet
  have hJ : MeasurableSet (Homeomorph.addRight (-a.2) '' B.interval) :=
    ((Homeomorph.addRight (-a.2)).isOpenMap _ B.interval_open).measurableSet
  have hfin : ν (q.nextFactorRebase d a.1 a.2 '' B.rectangle.second) ≠ ⊤ :=
    ((measure_mono (image_mono B.second_subset)).trans_lt
      (B.second_bound_compact.image (q.nextFactorRebase d a.1 a.2).continuous).measure_lt_top).ne
  erw [B.rebased_group_time_image c hf a]
  exact q.normalized_product_map_factor_of_finite d ν η _ _ hV hJ hfin

end PhysicalPrefixWindow
end DukePrimeDegree

end

end OAI
