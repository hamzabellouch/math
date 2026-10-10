import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixTimeExchange
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRootEmbeddings
import OAI.NumberTheory.DukePrimeDegree.Geometry.OpenRegionEmbedding

namespace OAI

/-! # Injective open regions in the exchanged prefix chart -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

def fullRectangleCoordinates (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :=
  (z.1.val,(z.2.1.val,z.2.2))

lemma fullRectangleCoordinates_isOpenEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.fullRectangleCoordinates q g k Q) :=
  Q.first_open.isOpenEmbedding_subtypeVal.prodMap
    (Q.second_open.isOpenEmbedding_subtypeVal.prodMap (Topology.IsOpenEmbedding.id (X := ℝ)))

def exchangedRectangleCoordinates (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × (Q.second × ℝ) → (UpperRootTransverse (d+1) × (T × ℝ)) × c.Time :=
  (prefixTimeExchange (T := T) q c hfinal) ∘ C.fullRectangleCoordinates q g k Q

lemma exchangedRectangleCoordinates_isOpenEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.exchangedRectangleCoordinates q g k c hfinal Q) :=
  (prefixTimeExchange (T := T) q c hfinal).isOpenEmbedding.comp
    (C.fullRectangleCoordinates_isOpenEmbedding q g k Q)

lemma exchangedRectangleCoordinates_param
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    (C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g
        (C.exchangedRectangleCoordinates q g k c hfinal Q z) =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z := by
  rw [exchangedRectangleCoordinates,Function.comp_apply,C.prefixTimeExchange_param]
  exact (C.rectangle_physicalParam_eq_extended q g k Q z).symm

def exchangedRectangleRegion (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (J : Set ℝ) : Set ((UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :=
  C.exchangedRectangleCoordinates q g k c hfinal Q '' (univ ×ˢ (univ ×ˢ J))

lemma exchangedRectangleRegion_open
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (J : Set ℝ) (hJ : IsOpen J) :
    IsOpen (C.exchangedRectangleRegion q g k c hfinal Q J) :=
  (C.exchangedRectangleCoordinates_isOpenEmbedding q g k c hfinal Q).isOpenMap _
    (isOpen_univ.prod (isOpen_univ.prod hJ))

lemma exchangedRectangleRegion_embedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    Topology.IsOpenEmbedding
      ((C.exchangedRectangleRegion q g k c hfinal Q J).domRestrict
        ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g)) := by
  apply openEmbedding_on_coordinate_image
    (C.exchangedRectangleCoordinates q g k c hfinal Q)
    ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g)
    (univ ×ˢ (univ ×ˢ J))
    (C.exchangedRectangleCoordinates_isOpenEmbedding q g k c hfinal Q)
    ((C.extend q.initial q.root q.mem_remaining q.least).timeParam_localHomeomorph
      c q.next_initial hfinal g) (isOpen_univ.prod (isOpen_univ.prod hJ))
  have he : (univ ×ˢ (univ ×ˢ J)).domRestrict
      (((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g) ∘
        C.exchangedRectangleCoordinates q g k c hfinal Q) =
      (univ ×ˢ (univ ×ˢ J)).domRestrict
        (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)) := by
    funext z
    exact C.exchangedRectangleCoordinates_param q g k c hfinal Q z.val
  rw [he]
  exact C.rectangle_param_isOpenEmbedding q g k Q A hA J hJ hwindow

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
