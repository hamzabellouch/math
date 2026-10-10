import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingFactorRebase

namespace OAI

/-! # Physical rectangles in the original remaining-subgroup time chart -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

def remainingFactorTime :
    (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) ≃ₜ c.Time :=
  q.remainingFactor.trans (c.remainingWordHomeomorph q.initial hf).symm

def physicalPrefixCoordinates {T : Type*} [TopologicalSpace T] :
    ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) ≃ₜ
      ((UpperRootTransverse (d+1) × T) × c.Time) :=
  (Homeomorph.refl _).prodCongr (remainingFactorTime q c hf)

variable {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

lemma physicalPrefixCoordinates_param
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    C.timeParam c q.initial hf g (physicalPrefixCoordinates (T := T) q c hf z) =
      q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z := by
  change C.quotientParam g (z.1.1,(z.1.2,
      c.remainingWordHomeomorph q.initial hf
        ((c.remainingWordHomeomorph q.initial hf).symm (q.remainingFactor z.2)))) = _
  erw [Homeomorph.apply_symm_apply,C.quotientParam_eq_action]
  change _ = rightAction (C.quotientParam g (z.1.1,(z.1.2,1))) _
  rw [C.quotientParam_eq_action]
  change _ = rightAction (rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) 1) _
  rw [rightAction_one]
  rfl

def originalRectangleCoordinates
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × (Q.second × ℝ) → (UpperRootTransverse (d+1) × T) × c.Time :=
  (physicalPrefixCoordinates (T := T) q c hf) ∘ C.fullRectangleCoordinates q g k Q

lemma originalRectangleCoordinates_openEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.originalRectangleCoordinates q c hf g k Q) :=
  (physicalPrefixCoordinates (T := T) q c hf).isOpenEmbedding.comp
    (C.fullRectangleCoordinates_isOpenEmbedding q g k Q)

lemma originalRectangleCoordinates_param
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    C.timeParam c q.initial hf g (C.originalRectangleCoordinates q c hf g k Q z) =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z := by
  rw [originalRectangleCoordinates,Function.comp_apply,physicalPrefixCoordinates_param]
  exact C.rectangle_includedFiberPoint q g k Q z

lemma originalRectangleCoordinates_image
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) (J : Set ℝ) :
    C.originalRectangleCoordinates q c hf g k Q '' (univ ×ˢ (univ ×ˢ J)) =
      Q.first ×ˢ (remainingFactorTime q c hf '' (Q.second ×ˢ J)) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.1.prop,(w.2.1.val,w.2.2),⟨w.2.1.prop,hw.2.2⟩,rfl⟩
  · rintro ⟨hs,w,hw,he⟩
    refine ⟨(⟨z.1,hs⟩,(⟨w.1,hw.1⟩,w.2)),⟨mem_univ _,mem_univ _,hw.2⟩,?_⟩
    exact Prod.ext rfl he

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
