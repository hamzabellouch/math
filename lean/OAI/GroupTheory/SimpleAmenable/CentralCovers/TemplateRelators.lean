import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SmallStarRelators

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualTemplateRelators

theorem sourceAlignedGroup_mono {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)) :
    Monotone (sourceAlignedGroup a r m hm M t) := by
  intro I J hIJ
  apply Subgroup.closure_mono
  rintro y ⟨b,hb,u,rfl⟩
  exact ⟨b,hb.trans hIJ,u,rfl⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

noncomputable def marginFamily (U : ι → polygonAlgebra a) (V : polygonAlgebra a) :
    Option ι → polygonAlgebra a
  | none => V
  | some i => V ⊓ U i

theorem actual_template_word_controls (hlarge : 25 ≤ m+1)
    (P : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) (U i).val)
    (hV : ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) V.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h V))
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15)
    (w : SmallFamilyWord (Fin (m+1)) ι) (hw : w ∈ smallFamilyLocal S)
    (hrel : smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1) :
    ∀ x ∈ f.range, Commute
      (copyFamilyEval (fun i => B.fullGeometricSector (by omega) P h (marginFamily U V i))
        (smallFamilyStarWord w)) x := by
  let masks := fun W : polygonAlgebra a => resolvedPolygonMask
    (primitiveTests (a := a) (r := r) P) W.val
  have he (i : Option ι) : masks (marginFamily U V i)=templateSides (fun i => masks (U i)) (masks V) i := by
    cases i with
    | none => rfl
    | some i => exact resolvedPolygonMask_inter _ V.val (U i).val hV (hU i)
  have hs i : SmallSupported (sourceAlignedGroup a r m hm M B.t)
      ((B.fullPrimitiveTable (by omega) P h).sector
        (templateSides (fun i => masks (U i)) (masks V) i)) := by
    rw [← he i]
    apply B.fullGeometricSector_supported
    cases i with
    | none => exact hV
    | some i => exact fun x y hh => and_congr (hV x y hh) (hU i x y hh)
  have hh := template_supported_word_controls _ (sourceAlignedGroup_mono B.t)
    B.c B.constant_aligned B.disjoint_aligned (B.fullPrimitiveTable (by omega) P h)
    (fun i => masks (U i)) (masks V) hs f hf hc S (by simp only [Fintype.card_fin]; omega)
    w hw hrel
  have heval : (fun i => B.fullGeometricSector (by omega) P h (marginFamily U V i))=
      (fun i => (B.fullPrimitiveTable (by omega) P h).sector
        (templateSides (fun i => masks (U i)) (masks V) i)) := by
    funext i
    exact congrArg ((B.fullPrimitiveTable (by omega) P h).sector) (he i)
  rw [heval]
  exact hh

end InitialCoverSystem
end ActualTemplateRelators

end SimpleAmenable
end
end

end OAI
