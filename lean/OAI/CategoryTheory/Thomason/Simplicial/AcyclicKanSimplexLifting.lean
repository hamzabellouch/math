import OAI.CategoryTheory.Thomason.Chains.FiniteChainMesh
import OAI.CategoryTheory.Thomason.Chains.NerveFaceChains
import OAI.CategoryTheory.Thomason.Gray.SimplicialHomotopyWhiskering
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSupportInclusion
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionBaseChange
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.KanFinitePosetExtension
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialApproximation
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Simplicial.WeakPathSurjectivity

namespace OAI

section

/-! # A common carrier for the prescribed boundary comparison

Both the label approximation and the exact iterated last-vertex boundary
remain in the original continuous boundary carrier. The ordered homotopy
between them therefore remains in that same carrier at every time.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity
open RelativeLabelCarrier ChainLabelApproximation

noncomputable section

variable (A B : PartOrd.{0}) [Finite A] [Fintype B]
variable {P : Type} [PartialOrder P]
variable (i : A →o B) (hi : Function.Injective i) (g : A →o P)
variable (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
variable (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
  (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)

include hi hF in
theorem iterated_realization_boundary (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A r))) :
    F (iteratedChainRealization B r
      ((SSet.toTop.map (nerveMap (iteratedMap i r).monotone.functor)).hom z)) =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom (iteratedChainRealization A r z) := by
  rw [← iteratedChainRealization_naturality i hi r z, hF]

include hi hF in
theorem label_boundary_carrier (r : ℕ) (label : iteratedChainPoset B r → P)
    (hlabel : MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset B r)
      (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
      0 < (PosetGeometry.coordinates P (F (iteratedChainRealization B r
        (RealizationPrism.simplexPoint (nerve (iteratedChainPoset B r)) s p)))).weights
          (label (s.obj k)))
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
    (PosetGeometry.coordinates P
      ((SSet.toTop.map (nerveMapOfLabels label hlabel)).hom
        ((SSet.toTop.map (nerveMap (iteratedMap i (r+1)).monotone.functor)).hom z))).weights.support ⊆
      (PosetGeometry.coordinates P
        ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
          (iteratedChainRealization A (r+1) z))).weights.support := by
  let := Fintype.ofFinite (iteratedChainPoset B r)
  have h := labelApproximation_support (F.comp (iteratedChainRealization B r))
    label hlabel hl ((SSet.toTop.map
      (nerveMap (iteratedMap i (r+1)).monotone.functor)).hom z)
  change _ ⊆ (PosetGeometry.coordinates P
    (F (iteratedChainRealization B (r+1)
      ((SSet.toTop.map (nerveMap (iteratedMap i (r+1)).monotone.functor)).hom z)))).weights.support at h
  rw [iterated_realization_boundary A B i hi g F hF] at h
  exact h

theorem greatest_boundary_carrier (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A r))) :
    (PosetGeometry.coordinates P
      ((SSet.toTop.map (nerveMap (g.comp (greatestVertex A r)).monotone.functor)).hom z)).weights.support ⊆
      (PosetGeometry.coordinates P
        ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
          (iteratedChainRealization A r z))).weights.support := by
  have h := coordinates_map_support_mono g _ _ (iterated_lastVertex_support_subset A r z)
  have he : (SSet.toTop.map (nerveMap (g.comp (greatestVertex A r)).monotone.functor)).hom z =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom
        ((SSet.toTop.map (nerveMap (greatestVertex A r).monotone.functor)).hom z) := by
    rw [orderNerveMap_comp, SSet.toTop.map_comp]
    rfl
  rw [he]
  exact h

def boundaryLabelOrderMap (r : ℕ) (label : iteratedChainPoset B r → P)
    (hlabel : MapsChains label) : iteratedChainPoset A (r+1) →o P :=
  (greatestLabel label hlabel).comp (NonemptyFiniteChains.orderHomMap (iteratedMap i r))

omit [Finite A] [Fintype B] in
theorem boundaryLabelOrderMap_comp (r : ℕ) (label : iteratedChainPoset B r → P)
    (hlabel : MapsChains label) :
    nerveMap (iteratedMap i (r+1)).monotone.functor ≫ nerveMapOfLabels label hlabel =
      nerveMap (boundaryLabelOrderMap A B i r label hlabel).monotone.functor :=
  (orderNerveMap_comp (NonemptyFiniteChains.orderHomMap (iteratedMap i r))
    (greatestLabel label hlabel)).symm

include hi hF in
theorem boundaryLabelOrderMap_le (r : ℕ) (label : iteratedChainPoset B r → P)
    (hlabel : MapsChains label)
    (hl : ∀ v, 0 < (PosetGeometry.coordinates P
      (F (iteratedChainRealization B r (posetVertexPoint v)))).weights (label v))
    (C : iteratedChainPoset A (r+1)) :
    boundaryLabelOrderMap A B i r label hlabel C ≤ g (greatestVertex A (r+1) C) := by
  apply greatestLabel_le label hlabel
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (NonemptyFiniteChains.mem_map_iff C (iteratedMap i r) y).mp hy
  exact (boundary_label_le i hi g F hF r label hl x).trans
    (g.monotone ((greatestVertex A r).monotone (le_greatest C x hx)))

include hi hF in
theorem boundaryLabelOrderMap_carrier (r : ℕ) (label : iteratedChainPoset B r → P)
    (hlabel : MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset B r)
      (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
      0 < (PosetGeometry.coordinates P (F (iteratedChainRealization B r
        (RealizationPrism.simplexPoint (nerve (iteratedChainPoset B r)) s p)))).weights
          (label (s.obj k)))
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
    (PosetGeometry.coordinates P
      ((SSet.toTop.map (nerveMap (boundaryLabelOrderMap A B i r label hlabel).monotone.functor)).hom z)).weights.support ⊆
      (PosetGeometry.coordinates P
        ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
          (iteratedChainRealization A (r+1) z))).weights.support := by
  have h := label_boundary_carrier A B i hi g F hF r label hlabel hl z
  have he := congrArg (fun k => k.hom z)
    ((congrArg SSet.toTop.map (boundaryLabelOrderMap_comp A B i r label hlabel).symm).trans
      (SSet.toTop.map_comp (nerveMap (iteratedMap i (r+1)).monotone.functor)
        (nerveMapOfLabels label hlabel)))
  rw [he]
  exact h

include hi hF in
theorem boundaryOrderHomotopy_carrier (r : ℕ) (label : iteratedChainPoset B r → P)
    (hlabel : MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset B r)
      (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
      0 < (PosetGeometry.coordinates P (F (iteratedChainRealization B r
        (RealizationPrism.simplexPoint (nerve (iteratedChainPoset B r)) s p)))).weights
          (label (s.obj k)))
    (hbound : ∀ C, boundaryLabelOrderMap A B i r label hlabel C ≤
      (g.comp (greatestVertex A (r+1))) C)
    (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
    (PosetGeometry.coordinates P
      (RealizedCylinder.homotopy (orderNerveHomotopy
        (boundaryLabelOrderMap A B i r label hlabel)
        (g.comp (greatestVertex A (r+1))) hbound) (t, z))).weights.support ⊆
      (PosetGeometry.coordinates P
        ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
          (iteratedChainRealization A (r+1) z))).weights.support := by
  intro y hy
  rcases PosetGeometry.orderNerveHomotopy_support
      (boundaryLabelOrderMap A B i r label hlabel)
      (g.comp (greatestVertex A (r+1))) hbound t z y
      (Finsupp.mem_support_iff.mp hy) with hy | hy
  · exact boundaryLabelOrderMap_carrier A B i hi g F hF r label hlabel hl z
      (Finsupp.mem_support_iff.mpr hy)
  · exact greatest_boundary_carrier A g (r+1) z (Finsupp.mem_support_iff.mpr hy)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The boundary paths of a relative approximation are coherent

The continuous label interpolation, ordered simplicial correction, and
barycentric last-vertex comparison lie in one boundary carrier. Their
triangle consequently has a homotopy which fixes both endpoints.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity
open RelativeLabelCarrier ChainLabelApproximation

noncomputable section

def boundaryBarycentricMap (A : PartOrd.{0}) [Finite A]
    {P : Type} [PartialOrder P] (g : A →o P) (r : ℕ) :
    C(SSet.toTop.obj (nerve (iteratedChainPoset A r)), SSet.toTop.obj (nerve P)) :=
  (SSet.toTop.map (nerveMap g.monotone.functor)).hom.comp (iteratedChainRealization A r)

variable (A B : PartOrd.{0}) [Finite A] [Fintype B]
variable {P : Type} [PartialOrder P] [Finite P]
variable (i : A →o B) (hi : Function.Injective i) (g : A →o P)
variable (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
variable (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
  (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)
variable (r : ℕ) (label : iteratedChainPoset B r → P) (hlabel : MapsChains label)
variable (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset B r)
  (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
  0 < (PosetGeometry.coordinates P (F (iteratedChainRealization B r
    (RealizationPrism.simplexPoint (nerve (iteratedChainPoset B r)) s p)))).weights
      (label (s.obj k)))

include hi hF hl in
def boundaryApproximationHomotopy :
    (boundaryBarycentricMap A g (r+1)).Homotopy
      (SSet.toTop.map (nerveMap
        (boundaryLabelOrderMap A B i r label hlabel).monotone.functor)).hom := by
  let := Fintype.ofFinite (iteratedChainPoset B r)
  let H := labelApproximationHomotopy (F.comp (iteratedChainRealization B r)) label hlabel hl
  let j := nerveMap (iteratedMap i (r+1)).monotone.functor
  have H' := H.comp (ContinuousMap.Homotopy.refl (SSet.toTop.map j).hom)
  refine H'.cast ?_ ?_
  · apply ContinuousMap.ext
    intro z
    exact iterated_realization_boundary A B i hi g F hF (r+1) z
  · exact congrArg TopCat.Hom.hom ((SSet.toTop.map_comp j
      (nerveMapOfLabels label hlabel)).symm.trans
        (congrArg SSet.toTop.map (boundaryLabelOrderMap_comp A B i r label hlabel)))

theorem boundaryApproximationHomotopy_support (t : unitInterval)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
    (PosetGeometry.coordinates P
      (boundaryApproximationHomotopy A B i hi g F hF r label hlabel hl (t, z))).weights.support ⊆
        (PosetGeometry.coordinates P (boundaryBarycentricMap A g (r+1) z)).weights.support := by
  let := Fintype.ofFinite (iteratedChainPoset B r)
  let w := (SSet.toTop.map (nerveMap (iteratedMap i (r+1)).monotone.functor)).hom z
  have h := PosetGeometry.commonChainHomotopy_support
    ((F.comp (iteratedChainRealization B r)).comp (chainRealizationMap (iteratedChainPoset B r)))
    (SSet.toTop.map (nerveMapOfLabels label hlabel)).hom
    (fun w => PosetGeometry.compatibleSupport_of_subset _ _
      (PosetGeometry.coordinates_chainSupported _)
      (labelApproximation_support (F.comp (iteratedChainRealization B r)) label hlabel hl w))
    (fun w => PosetGeometry.coordinates P (F (iteratedChainRealization B r
      (chainRealizationMap (iteratedChainPoset B r) w))))
    (fun _ => Finset.Subset.refl _)
    (labelApproximation_support (F.comp (iteratedChainRealization B r)) label hlabel hl) t w
  have he : F (iteratedChainRealization B r (chainRealizationMap (iteratedChainPoset B r) w)) =
      boundaryBarycentricMap A g (r+1) z :=
    iterated_realization_boundary A B i hi g F hF (r+1) z
  rw [he] at h
  exact h

def boundaryLastVertexHomotopy :
    (boundaryBarycentricMap A g (r+1)).Homotopy
      (SSet.toTop.map (nerveMap (g.comp (greatestVertex A (r+1))).monotone.functor)).hom := by
  have H := (ContinuousMap.Homotopy.refl
    (SSet.toTop.map (nerveMap g.monotone.functor)).hom).comp (iteratedCarrierHomotopy A (r+1))
  refine H.cast rfl ?_
  exact congrArg TopCat.Hom.hom ((SSet.toTop.map_comp
    (nerveMap (greatestVertex A (r+1)).monotone.functor)
    (nerveMap g.monotone.functor)).symm.trans
      (congrArg SSet.toTop.map (orderNerveMap_comp (greatestVertex A (r+1)) g).symm))

omit [Finite P] in
theorem boundaryLastVertexHomotopy_support (t : unitInterval)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
    (PosetGeometry.coordinates P (boundaryLastVertexHomotopy A g r (t, z))).weights.support ⊆
      (PosetGeometry.coordinates P (boundaryBarycentricMap A g (r+1) z)).weights.support :=
  iteratedCarrierHomotopy_map_support A (r+1) g t z

include hi hF hl in
def boundaryOrderedHomotopy :
    SSet.Homotopy
      (nerveMap (boundaryLabelOrderMap A B i r label hlabel).monotone.functor)
      (nerveMap (g.comp (greatestVertex A (r+1))).monotone.functor) :=
  orderNerveHomotopy _ _ (boundaryLabelOrderMap_le A B i hi g F hF r label hlabel
    (fun v => hl 0 (PosetGeometry.vertex v) (StdSimplex.single 0) 0))

def boundaryApproximationTriangle :
    ((boundaryApproximationHomotopy A B i hi g F hF r label hlabel hl).trans
      (RealizedCylinder.homotopy (boundaryOrderedHomotopy A B i hi g F hF r label hlabel hl))).toContinuousMap.HomotopyRel
      (boundaryLastVertexHomotopy A g r).toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1} := by
  let T := PosetGeometry.carrierTriangle
    (boundaryApproximationHomotopy A B i hi g F hF r label hlabel hl)
    (RealizedCylinder.homotopy (boundaryOrderedHomotopy A B i hi g F hF r label hlabel hl))
    (boundaryLastVertexHomotopy A g r) (boundaryBarycentricMap A g (r+1))
    (boundaryApproximationHomotopy_support A B i hi g F hF r label hlabel hl)
    (boundaryOrderHomotopy_carrier A B i hi g F hF r label hlabel hl _)
    (boundaryLastVertexHomotopy_support A g r)
  refine { toHomotopy := T.toHomotopy, prop' := ?_ }
  intro t z hz
  exact T.prop t z (hz.elim Or.inl (fun h => Or.inr (Or.inl h)))

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Nullity of the boundary loop in relative approximation

The inverse barycentric comparison, label interpolation, and ordered
correction form a closed boundary path. The entire path lies in the
original barycentric carrier, so it contracts with both ends fixed.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity
open RelativeLabelCarrier ChainLabelApproximation

noncomputable section

variable (A B : PartOrd.{0}) [Finite A] [Fintype B]
variable {P : Type} [PartialOrder P] [Finite P]
variable (i : A →o B) (hi : Function.Injective i) (g : A →o P)
variable (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
variable (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
  (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)
variable (r : ℕ) (label : iteratedChainPoset B r → P) (hlabel : MapsChains label)
variable (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset B r)
  (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
  0 < (PosetGeometry.coordinates P (F (iteratedChainRealization B r
    (RealizationPrism.simplexPoint (nerve (iteratedChainPoset B r)) s p)))).weights
      (label (s.obj k)))

include hi hF hl in
def boundaryApproximationLoop :
    let l := (SSet.toTop.map (nerveMap
      (g.comp (greatestVertex A (r+1))).monotone.functor)).hom
    l.Homotopy l :=
  ((boundaryLastVertexHomotopy A g r).symm.trans
    (boundaryApproximationHomotopy A B i hi g F hF r label hlabel hl)).trans
      (RealizedCylinder.homotopy (boundaryOrderedHomotopy A B i hi g F hF r label hlabel hl))

theorem boundaryApproximationLoop_support (t : unitInterval)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
    (PosetGeometry.coordinates P
      (boundaryApproximationLoop A B i hi g F hF r label hlabel hl (t, z))).weights.support ⊆
      (PosetGeometry.coordinates P (boundaryBarycentricMap A g (r+1) z)).weights.support := by
  apply PosetGeometry.homotopy_trans_support
  · apply PosetGeometry.homotopy_trans_support
    · intro t z
      exact boundaryLastVertexHomotopy_support A g r (unitInterval.symm t) z
    · exact boundaryApproximationHomotopy_support A B i hi g F hF r label hlabel hl
  · exact boundaryOrderHomotopy_carrier A B i hi g F hF r label hlabel hl _

def boundaryApproximationLoop_null :
    (boundaryApproximationLoop A B i hi g F hF r label hlabel hl).toContinuousMap.HomotopyRel
      (ContinuousMap.Homotopy.refl (SSet.toTop.map (nerveMap
        (g.comp (greatestVertex A (r+1))).monotone.functor)).hom).toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1} := by
  let c := boundaryBarycentricMap A g (r+1)
  let H := boundaryApproximationLoop A B i hi g F hF r label hlabel hl
  let G := ContinuousMap.Homotopy.refl (SSet.toTop.map (nerveMap
    (g.comp (greatestVertex A (r+1))).monotone.functor)).hom
  let D := PosetGeometry.commonCarrierHomotopyRel H G ∅ (by simp)
    (c.comp ⟨Prod.snd, continuous_snd⟩)
    (fun z => boundaryApproximationLoop_support A B i hi g F hF r label hlabel hl z.1 z.2)
    (fun z => greatest_boundary_carrier A g (r+1) z.2)
  refine { toHomotopy := D.toHomotopy, prop' := ?_ }
  intro t z hz
  exact D.prop t z (hz.elim Or.inl (fun h => Or.inr (Or.inl h)))

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Relative Kan approximation with its actual comparison class

The finite-stage approximation has the exact last-vertex boundary.
Its comparison homotopy to the given continuous map fixes that boundary.
The boundary loop is contracted in its original poset carrier before
the topological homotopy extension theorem straightens the comparison.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity MonoidalCategory
open RelativeLabelCarrier ChainLabelApproximation

noncomputable section

theorem relative_kan_approximation_stage
    (A B : PartOrd.{0}) [Finite A] [Fintype B]
    {P : Type} [PartialOrder P] [Finite P]
    (i : A →o B) (hi : Function.Injective i) (g : A →o P)
    (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
    (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)
    (r : ℕ) (label : iteratedChainPoset B r → P) (hlabel : MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset B r)
      (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
      0 < (PosetGeometry.coordinates P (F (iteratedChainRealization B r
        (RealizationPrism.simplexPoint (nerve (iteratedChainPoset B r)) s p)))).weights
          (label (s.obj k)))
    {X : SSet.{0}} [SSet.KanComplex X] (k : nerve P ⟶ X) :
    ∃ d : nerve (iteratedChainPoset B (r+1)) ⟶ X,
      nerveMap (iteratedMap i (r+1)).monotone.functor ≫ d =
        nerveMap (g.comp (greatestVertex A (r+1))).monotone.functor ≫ k ∧
      Nonempty (ContinuousMap.HomotopyRel
        (((SSet.toTop.map k).hom.comp F).comp
          (SSet.toTop.map (nerveMap (greatestVertex B (r+1)).monotone.functor)).hom)
          (SSet.toTop.map d).hom
          (Set.range (SSet.toTop.map (nerveMap (iteratedMap i (r+1)).monotone.functor)).hom)) := by
  let := Fintype.ofFinite (iteratedChainPoset B r)
  let j := nerveMap (iteratedMap i (r+1)).monotone.functor
  let : Mono j := SubdivisionHornFaces.nerveMap_mono (iteratedMap i (r+1))
    (iteratedMap_injective i hi (r+1))
  let f := nerveMapOfLabels label hlabel
  let v := nerveMap (g.comp (greatestVertex A (r+1))).monotone.functor
  let O := boundaryOrderedHomotopy A B i hi g F hF r label hlabel hl
  have h₀ : SSet.ι₀ ≫ (O.h ≫ k) = j ≫ (f ≫ k) := by
    rw [← Category.assoc, O.h₀]
    rw [← boundaryLabelOrderMap_comp A B i r label hlabel]
    exact Category.assoc j f k
  obtain ⟨e, he₀, hej⟩ := exists_kan_homotopy_extension j (f ≫ k) (O.h ≫ k) h₀
  let d := SSet.ι₁ ≫ e
  let C : SSet.Homotopy (f ≫ k) d := {
    h := e
    h₀ := he₀
    h₁ := rfl
    rel := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  have hd : j ≫ d = v ≫ k := by
    have hn : j ≫ SSet.ι₁ = SSet.ι₁ ≫ j ▷ SSet.stdSimplex.obj (.mk 1) := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    change j ≫ (SSet.ι₁ ≫ e) = _
    rw [← Category.assoc, hn, Category.assoc, hej, ← Category.assoc, O.h₁]
  let Fk := (SSet.toTop.map k).hom.comp F
  let L := nerveMap (greatestVertex B (r+1)).monotone.functor
  let H₀ := (ContinuousMap.Homotopy.refl Fk).comp (iteratedCarrierHomotopy B (r+1)).symm
  let H₁ : (Fk.comp (iteratedChainRealization B (r+1))).Homotopy
      (SSet.toTop.map (f ≫ k)).hom := by
    let H := (ContinuousMap.Homotopy.refl (SSet.toTop.map k).hom).comp
      (labelApproximationHomotopy (F.comp (iteratedChainRealization B r)) label hlabel hl)
    refine H.cast (by ext; rfl) ?_
    exact congrArg TopCat.Hom.hom (SSet.toTop.map_comp f k).symm
  let H := (H₀.trans H₁).trans (RealizedCylinder.homotopy C)
  let Q := boundaryApproximationLoop A B i hi g F hF r label hlabel hl
  have hs₀ (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
      H₀ (t, (SSet.toTop.map j).hom z) =
        (SSet.toTop.map k).hom ((boundaryLastVertexHomotopy A g r).symm (t, z)) := by
    change (SSet.toTop.map k).hom (F (iteratedCarrierHomotopy B (r+1)
      (unitInterval.symm t, (SSet.toTop.map j).hom z))) = _
    rw [← iteratedCarrierHomotopy_naturality i hi (r+1), hF]
    rfl
  have hs₁ (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
      H₁.toContinuousMap (t, (SSet.toTop.map j).hom z) =
        (SSet.toTop.map k).hom
          (boundaryApproximationHomotopy A B i hi g F hF r label hlabel hl (t, z)) := rfl
  have hs₂ (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
      RealizedCylinder.homotopy C (t, (SSet.toTop.map j).hom z) =
        (SSet.toTop.map k).hom (RealizedCylinder.homotopy O (t, z)) :=
    realized_homotopy_square C O j k hej t z
  have hs (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
      H.toContinuousMap (t, (SSet.toTop.map j).hom z) = (SSet.toTop.map k).hom (Q (t, z)) :=
    homotopy_trans_pointwise _ _ _ _ _ _
      (homotopy_trans_pointwise _ _ _ _ _ _ hs₀ hs₁) hs₂ t z
  let f₀ := TopCat.ofHom (Fk.comp (SSet.toTop.map L).hom)
  have hc (z : SSet.toTop.obj (nerve (iteratedChainPoset A (r+1)))) :
      f₀.hom ((SSet.toTop.map j).hom z) = (SSet.toTop.map k).hom ((SSet.toTop.map v).hom z) := by
    exact (H.map_zero_left _).symm.trans ((hs 0 z).trans
      (congrArg (SSet.toTop.map k).hom (Q.map_zero_left z)))
  let D₀ := boundaryApproximationLoop_null A B i hi g F hF r label hlabel hl
  let D : (RealizationHomotopyRectification.restrictionAlong j H).HomotopyRel
      (RealizationHomotopyRectification.constantSideAlong j f₀)
      {z | z.1 = 0 ∨ z.1 = 1} := {
    toHomotopy := {
      toContinuousMap := ⟨fun z => (SSet.toTop.map k).hom (D₀ z), by fun_prop⟩
      map_zero_left := by
        intro z
        exact (congrArg (SSet.toTop.map k).hom (D₀.map_zero_left z)).trans
          (hs z.1 z.2).symm
      map_one_left := by
        intro z
        exact (congrArg (SSet.toTop.map k).hom (D₀.map_one_left z)).trans
          (hc z.2).symm }
    prop' := by
      intro t z hz
      exact (congrArg (SSet.toTop.map k).hom (D₀.prop t z hz)).trans (hs z.1 z.2).symm }
  exact ⟨d, hd, RealizationHomotopyRectification.straighten_mono j f₀ (SSet.toTop.map d) H D⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Relative Kan approximation on the actual finite subdivision

Choosing the finite labels and transporting the chain-nerve construction
through the subdivision isomorphism retains both the exact boundary and
the full relative realization homotopy.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder
open RelativeLabelCarrier

noncomputable section

theorem exists_relative_kan_approximation
    (A B : PartOrd.{0}) [Finite A] [Fintype B]
    {P : Type} [PartialOrder P] [Finite P]
    (i : A →o B) (hi : Function.Injective i) (g : A →o P)
    (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
    (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)
    {X : SSet.{0}} [SSet.KanComplex X] (k : nerve P ⟶ X) :
    ∃ (r : ℕ) (d : (iteratedSubdivision r).obj (nerve B) ⟶ X),
      (iteratedSubdivision r).map (nerveMap i.monotone.functor) ≫ d =
        iteratedLastVertex (nerve A) r ≫ nerveMap g.monotone.functor ≫ k ∧
      Nonempty ((((SSet.toTop.map k).hom.comp F).comp
          (SSet.toTop.map (iteratedLastVertex (nerve B) r)).hom).HomotopyRel
        (SSet.toTop.map d).hom
        (Set.range (SSet.toTop.map
          ((iteratedSubdivision r).map (nerveMap i.monotone.functor))).hom)) := by
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels B P F
  obtain ⟨d, hd, ⟨H⟩⟩ := relative_kan_approximation_stage A B i hi g F hF
    r label hlabel hl k
  let eA := iteratedSubdivisionNerveIso A (r+1)
  let eB := iteratedSubdivisionNerveIso B (r+1)
  let j := nerveMap (iteratedMap i (r+1)).monotone.functor
  let ir := (iteratedSubdivision (r+1)).map (nerveMap i.monotone.functor)
  have hn : ir ≫ eB.hom = eA.hom ≫ j := iteratedSubdivisionNerveIso_naturality i (r+1)
  have hd' : ir ≫ (eB.hom ≫ d) =
      iteratedLastVertex (nerve A) (r+1) ≫ nerveMap g.monotone.functor ≫ k := by
    rw [← Category.assoc, hn, Category.assoc, hd,
      orderNerveMap_comp, ← Category.assoc, ← Category.assoc,
      greatestVertex_lastVertex]
    exact Category.assoc _ _ _
  let Fk := (SSet.toTop.map k).hom.comp F
  have h0 : ((Fk.comp
      (SSet.toTop.map (nerveMap (greatestVertex B (r+1)).monotone.functor)).hom).comp
        (SSet.toTop.map eB.hom).hom) =
      Fk.comp (SSet.toTop.map (iteratedLastVertex (nerve B) (r+1))).hom := by
    rw [ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← SSet.toTop.map_comp,
      greatestVertex_lastVertex]
  have h1 : (SSet.toTop.map d).hom.comp (SSet.toTop.map eB.hom).hom =
      (SSet.toTop.map (eB.hom ≫ d)).hom := by
    rw [SSet.toTop.map_comp]
    rfl
  have himage (x : SSet.toTop.obj ((iteratedSubdivision (r+1)).obj (nerve B)))
      (hx : x ∈ Set.range (SSet.toTop.map ir).hom) :
      (SSet.toTop.map eB.hom).hom x ∈ Set.range (SSet.toTop.map j).hom := by
    obtain ⟨z, rfl⟩ := hx
    refine ⟨(SSet.toTop.map eA.hom).hom z, ?_⟩
    have he := congrArg (fun q => (SSet.toTop.map q).hom z) hn
    simp only [SSet.toTop.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply] at he
    exact he.symm
  refine ⟨r+1, eB.hom ≫ d, hd', ⟨{
    toHomotopy := (H.toHomotopy.comp
      (ContinuousMap.Homotopy.refl (SSet.toTop.map eB.hom).hom)).cast h0 h1
    prop' := ?_ }⟩⟩
  intro t x hx
  exact (H.prop t _ (himage x hx)).trans (congrArg (fun q => q x) h0)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The face-poset comparison for simplex subcomplexes

The finite-chain description of the actual subdivision restricts to the
nondegenerate faces of every simplex subcomplex.  Its comparison to the
original simplicial set is exactly the last-vertex map, and the construction
commutes with inclusions of subcomplexes.
-/

namespace Thomason.Construction.SubcomplexFaceComparison

open CategoryTheory PartialOrder Opposite
open NonsingularLastVertex ChainLabelApproximation
open scoped Simplicial

noncomputable section

def ambientFace (n : ℕ) :
    NonemptyFiniteChains (ULift.{0} (Fin (n+1))) →o (Δ[n] : SSet.{0}).N where
  toFun C := faceMap ((SSet.stdSimplex.isoNerve.{0} n).inv)
    (preservesNondegenerate_of_mono _) (NerveFaceChains.faceOfChain C)
  monotone' C D h := by
    apply (faceMap ((SSet.stdSimplex.isoNerve.{0} n).inv)
      (preservesNondegenerate_of_mono _)).monotone
    apply (NerveFaceChains.chainOfFace_le_iff _ _).mp
    rw [NerveFaceChains.chainOfFace_faceOfChain,
      NerveFaceChains.chainOfFace_faceOfChain]
    exact h

theorem ambientFace_simplex (n : ℕ)
    (C : NonemptyFiniteChains (ULift.{0} (Fin (n+1)))) :
    (ambientFace n C).simplex =
      ((SSet.stdSimplex.isoNerve.{0} n).inv).app
        (.op (.mk (ChainOrdinal.choose C).dim))
        (SubdivisionBarycentric.finiteChainSimplex C) := rfl

theorem ambientFace_eq (n : ℕ) : ambientFace n =
    (faceMap ((SSet.stdSimplex.isoNerve.{0} n).inv)
      (preservesNondegenerate_of_mono _)).comp
      (NerveFaceChains.orderIso (ULift.{0} (Fin (n+1)))).symm.toOrderEmbedding.toOrderHom := by
  ext C
  have h : NerveFaceChains.faceOfChain C =
      (NerveFaceChains.orderIso (ULift.{0} (Fin (n+1)))).symm C := by
    apply (NerveFaceChains.orderIso (ULift.{0} (Fin (n+1)))).injective
    rw [OrderIso.apply_symm_apply]
    exact NerveFaceChains.chainOfFace_faceOfChain C
  exact congrArg (faceMap (SSet.stdSimplex.isoNerve.{0} n).inv
    (preservesNondegenerate_of_mono _)) h

theorem ambientFace_mem {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex)
    (C : faceFamilyVertices (subcomplexFaceFamily A)) :
    (ambientFace n C.val).simplex ∈ A.obj _ := by
  classical
  obtain ⟨S, hS, hC⟩ := C.property
  apply (Finset.mem_filter.mp hS).2
  apply (SSet.stdSimplex.mem_face_iff S _).mpr
  rw [ambientFace_simplex]
  intro i
  exact hC _ (((ChainOrdinal.choose C.val).enum i).property)

def face {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    faceFamilyVertices (subcomplexFaceFamily A) →o A.toSSet.N where
  toFun C := SSet.N.mk ⟨(ambientFace n C.val).simplex, ambientFace_mem A C⟩
    ((A.mem_nonDegenerate_iff _).mpr (ambientFace n C.val).nonDegenerate)
  monotone' C D h := by
    obtain ⟨u, hu, he⟩ := SSet.N.le_iff_exists_mono.mp ((ambientFace n).monotone h)
    apply SSet.N.le_iff_exists_mono.mpr
    exact ⟨u, hu, Subtype.ext he⟩

def forget {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    faceFamilyVertices (subcomplexFaceFamily A) →o
      NonemptyFiniteChains (ULift.{0} (Fin (n+1))) where
  toFun C := C.val
  monotone' _ _ h := h

theorem face_ambient {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    (faceMap A.ι (preservesNondegenerate_of_mono _)).comp (face A) =
      (ambientFace n).comp (forget A) := by
  ext C
  rfl

def chainLastVertex (n : ℕ) :
    nerve (NonemptyFiniteChains (ULift.{0} (Fin (n+1)))) ⟶ (Δ[n] : SSet.{0}) :=
  nerveMap (chainMaximumHom (X := ULift.{0} (Fin (n+1)))).monotone.functor ≫
    (SSet.stdSimplex.isoNerve.{0} n).inv

theorem ambientFace_lastVertex (n : ℕ) :
    nerveMap (ambientFace n).monotone.functor ≫ NonsingularLastVertex.map (Δ[n]) =
      chainLastVertex n := by
  rw [ambientFace_eq, orderNerveMap_comp, Category.assoc, map_naturality,
    ← Category.assoc, NerveFaceChains.lastVertex_eq]
  change ((NerveFaceChains.nerveIso (ULift.{0} (Fin (n+1)))).inv ≫
    ((NerveFaceChains.nerveIso (ULift.{0} (Fin (n+1)))).hom ≫
      nerveMap greatestHom.monotone.functor)) ≫
        (SSet.stdSimplex.isoNerve.{0} n).inv =
    nerveMap (chainMaximumHom (X := ULift.{0} (Fin (n+1)))).monotone.functor ≫
      (SSet.stdSimplex.isoNerve.{0} n).inv
  rw [Iso.inv_hom_id_assoc]
  have hg : (greatestHom (P := ULift.{0} (Fin (n+1)))) = chainMaximumHom := by
    apply DFunLike.ext
    intro C
    exact greatest_eq_chainMaximum C
  rw [hg]

def standardIntoChains (n : ℕ) :
    SSet.sd.obj (Δ[n] : SSet.{0}) ⟶ nerve (NonemptyFiniteChains (ULift.{0} (Fin (n+1)))) :=
  SSet.stdSimplex.sdIso.hom.app (.mk n)

def chainInclusion {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.sd.obj A.toSSet ⟶ nerve (NonemptyFiniteChains (ULift.{0} (Fin (n+1)))) :=
  SSet.sd.map A.ι ≫ standardIntoChains n

theorem chainInclusion_fac {n : ℕ} {A B : (Δ[n] : SSet.{0}).Subcomplex} (h : A ≤ B) :
    SSet.sd.map (SSet.Subcomplex.homOfLE h) ≫ chainInclusion B = chainInclusion A := by
  unfold chainInclusion
  rw [← Category.assoc, ← SSet.sd.map_comp, SSet.Subcomplex.homOfLE_ι]

theorem firstSubdivision_inclusion {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    (subcomplexFirstSubdivisionIso A).hom ≫
        nerveMap (fullSubposetInclusion (faceFamilyVertices (subcomplexFaceFamily A))) =
      chainInclusion A := by
  have h (F : Finset (Finset (Fin (n+1)))) :
      (faceUnionSubdivisionIso F).hom ≫
          nerveMap (fullSubposetInclusion (faceFamilyVertices F)) =
        chainInclusion (faceUnion F) := by
    let R : (nerve (NonemptyFiniteChains (ULift.{0} (Fin (n+1))))).Subcomplex :=
      subdividedFaceUnion F
    let U : (nerve (NonemptyFiniteChains (ULift.{0} (Fin (n+1))))).Subcomplex :=
      fullSubposetComplex (faceFamilyVertices F)
    let e₁ : SSet.sd.obj (faceUnion F).toSSet ≅ R.toSSet :=
      SubdivisionBarycentric.faceUnionSubdivisionRangeIso F
    let e₂ : R.toSSet ≅ U.toSSet :=
      SSet.Subcomplex.eqToIso (subdividedFaceUnion_eq_full F)
    let e₃ : nerve (faceFamilyVertices F) ≅ U.toSSet :=
      fullSubposetComplexIso (faceFamilyVertices F)
    have he₃ : e₃.hom ≫ U.ι =
        nerveMap (fullSubposetInclusion (faceFamilyVertices F)) := by
      simp [e₃, U, fullSubposetComplexIso]
    have he₂ : e₂.hom ≫ U.ι = R.ι := by
      simp [e₂, SSet.Subcomplex.eqToIso]
    have he₁ : e₁.hom ≫ R.ι = chainInclusion (faceUnion F) :=
      SubdivisionBarycentric.faceUnionSubdivisionRangeIso_inclusion F
    change ((e₁.hom ≫ e₂.hom) ≫ e₃.inv) ≫ _ = _
    rw [← he₃]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, he₂, he₁]
  change (SSet.sd.map (SSet.Subcomplex.eqToIso
      (faceUnion_subcomplexFaceFamily A).symm).hom ≫
    (faceUnionSubdivisionIso (subcomplexFaceFamily A)).hom) ≫ _ = _
  rw [Category.assoc, h]
  change SSet.sd.map (SSet.Subcomplex.eqToIso
      (faceUnion_subcomplexFaceFamily A).symm).hom ≫
    (SSet.sd.map (faceUnion (subcomplexFaceFamily A)).ι ≫ standardIntoChains n) =
      SSet.sd.map A.ι ≫ standardIntoChains n
  rw [← Category.assoc, ← SSet.sd.map_comp]
  congr 1

def map {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.sd.obj A.toSSet ⟶ nerve A.toSSet.N :=
  (subcomplexFirstSubdivisionIso A).hom ≫ nerveMap (face A).monotone.functor

theorem map_ambient {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    map A ≫ nerveMap (faceMap A.ι (preservesNondegenerate_of_mono _)).monotone.functor =
      chainInclusion A ≫ nerveMap (ambientFace n).monotone.functor := by
  unfold map
  rw [Category.assoc, ← orderNerveMap_comp, face_ambient, orderNerveMap_comp,
    ← Category.assoc]
  change ((subcomplexFirstSubdivisionIso A).hom ≫
    nerveMap (fullSubposetInclusion (faceFamilyVertices (subcomplexFaceFamily A)))) ≫
      nerveMap (ambientFace n).monotone.functor = _
  rw [firstSubdivision_inclusion]

@[reassoc]
theorem map_lastVertex {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    map A ≫ NonsingularLastVertex.map A.toSSet = lastVertex.app A.toSSet := by
  apply (cancel_mono A.ι).mp
  rw [Category.assoc, ← NonsingularLastVertex.map_naturality A.ι
    (preservesNondegenerate_of_mono A.ι), ← Category.assoc, map_ambient,
    Category.assoc, ambientFace_lastVertex]
  unfold chainInclusion
  rw [Category.assoc]
  have he : standardIntoChains n ≫ chainLastVertex n =
      lastVertex.app (Δ[n] : SSet.{0}) :=
    lastVertex_standard_formula (.mk n)
  rw [he]
  exact lastVertex.naturality A.ι

@[reassoc]
theorem map_naturality {n : ℕ} {A B : (Δ[n] : SSet.{0}).Subcomplex} (h : A ≤ B) :
    SSet.sd.map (SSet.Subcomplex.homOfLE h) ≫ map B =
      map A ≫ nerveMap (faceMap (SSet.Subcomplex.homOfLE h)
        (preservesNondegenerate_of_mono _)).monotone.functor := by
  apply (cancel_mono
    (nerveMap (faceMap B.ι (preservesNondegenerate_of_mono _)).monotone.functor)).mp
  rw [Category.assoc, map_ambient, ← Category.assoc, chainInclusion_fac]
  rw [Category.assoc, ← orderNerveMap_comp]
  have he : (faceMap B.ι (preservesNondegenerate_of_mono _)).comp
      (faceMap (SSet.Subcomplex.homOfLE h) (preservesNondegenerate_of_mono _)) =
      faceMap A.ι (preservesNondegenerate_of_mono _) := by
    ext C
    rfl
  rw [he, map_ambient]

end

end Thomason.Construction.SubcomplexFaceComparison

end

section

/-! # Literal twice-subdivided attaching pairs

The source and target identifications commute with the actual inclusion of
any simplex subcomplex. In particular they apply to every horn and boundary.
-/

namespace Thomason.Construction.DoubleSubdivisionPairs

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

abbrev Faces (n : ℕ) := NonemptyFiniteChains (ULift.{0} (Fin (n+1)))

def oldFaces {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) : Set (Faces n) :=
  faceFamilyVertices (subcomplexFaceFamily A)

def targetIso (n : ℕ) :
    SSet.sd.obj (SSet.sd.obj (Δ[n] : SSet.{0})) ≅ nerve (NonemptyFiniteChains (Faces n)) := by
  let : Finite (Faces n) := finite_nonemptyFiniteChains _
  exact SSet.sd.mapIso (SSet.stdSimplex.sdIso.app (.mk n)) ≪≫ NerveSubdivisionMap.iso (Faces n)

def orderNerveIso {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : nerve P ≅ nerve Q :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk (α := PartOrd.of P) (β := PartOrd.of Q) e)

def sourceIso {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.sd.obj (SSet.sd.obj A.toSSet) ≅ nerve (ChainSieve.old (oldFaces A)) := by
  let : Finite (Faces n) := finite_nonemptyFiniteChains _
  exact SSet.sd.mapIso (subcomplexFirstSubdivisionIso A) ≪≫
    NerveSubdivisionMap.iso (oldFaces A) ≪≫
      orderNerveIso (ChainSieve.subsetIso (oldFaces A))

/-- The two identifications identify the actual twice-subdivided map,
not just its source and target up to unrelated equivalences. -/
theorem inclusion {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    (sourceIso A).hom ≫ nerveMap (subposetInclusion (ChainSieve.old (oldFaces A))).monotone.functor =
      SSet.sd.map (SSet.sd.map A.ι) ≫ (targetIso n).hom := by
  let : Finite (Faces n) := finite_nonemptyFiniteChains _
  have hfirst : (subcomplexFirstSubdivisionIso A).hom ≫
      nerveMap (subposetInclusion (oldFaces A)).monotone.functor =
      SSet.sd.map A.ι ≫ (SSet.stdSimplex.sdIso.app (.mk n)).hom :=
    SubcomplexFaceComparison.firstSubdivision_inclusion A
  have hchain :
      (orderNerveIso (ChainSieve.subsetIso (oldFaces A))).hom ≫
        nerveMap (subposetInclusion (ChainSieve.old (oldFaces A))).monotone.functor =
      NerveSubdivisionMap.chainNerveMap (subposetInclusion (oldFaces A)) := by
    change nerveMap (ChainSieve.subsetIso (oldFaces A)).toOrderEmbedding.toOrderHom.monotone.functor ≫
      nerveMap (subposetInclusion (ChainSieve.old (oldFaces A))).monotone.functor = _
    rw [← orderNerveMap_comp, ChainSieve.subsetIso_inclusion]
    rfl
  have hnat := NerveSubdivisionMap.map_naturality (subposetInclusion (oldFaces A))
  simp only [sourceIso, targetIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change SSet.sd.map (subcomplexFirstSubdivisionIso A).hom ≫
      NerveSubdivisionMap.map (oldFaces A) ≫
        (orderNerveIso (ChainSieve.subsetIso (oldFaces A))).hom ≫
          nerveMap (subposetInclusion (ChainSieve.old (oldFaces A))).monotone.functor =
    SSet.sd.map (SSet.sd.map A.ι) ≫
      SSet.sd.map (SSet.stdSimplex.sdIso.app (.mk n)).hom ≫ NerveSubdivisionMap.map (Faces n)
  rw [hchain]
  have hf := congrArg (fun k => SSet.sd.map k ≫ NerveSubdivisionMap.map (Faces n)) hfirst
  simp only [SSet.sd.map_comp, Category.assoc] at hf
  have ht : SSet.sd.map (SSet.sd.map A.ι ≫ (SSet.stdSimplex.sdIso.app (.mk n)).hom) ≫
      NerveSubdivisionMap.map (Faces n) =
      SSet.sd.map (SSet.sd.map A.ι) ≫ SSet.sd.map (SSet.stdSimplex.sdIso.app (.mk n)).hom ≫
        NerveSubdivisionMap.map (Faces n) :=
    (congrArg (fun k => k ≫ NerveSubdivisionMap.map (Faces n))
      (SSet.sd.map_comp (SSet.sd.map A.ι) (SSet.stdSimplex.sdIso.app (.mk n)).hom)).trans
        (Category.assoc _ _ _)
  exact (congrArg (fun k => SSet.sd.map (subcomplexFirstSubdivisionIso A).hom ≫ k)
    hnat.symm).trans (hf.trans ht)

end

end Thomason.Construction.DoubleSubdivisionPairs

end

section

/-! # Exact Kan extensions from continuous simplex-boundary extensions

The geometric extension is converted to a finite ordered extension, then
to a simplicial extension in the original Kan target. The actual
last-vertex identities remove both face-poset parameters and subdivision.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

theorem kan_extension_of_subcomplex_realization_extension {n : ℕ}
    (A B : (Δ[n] : SSet.{0}).Subcomplex) (hAB : A ≤ B)
    {X : SSet.{0}} [SSet.KanComplex X] (a : A.toSSet ⟶ X)
    (b : SSet.toTop.obj B.toSSet ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫ b = SSet.toTop.map a) :
    ∃ d : B.toSSet ⟶ X, SSet.Subcomplex.homOfLE hAB ≫ d = a := by
  let i := SSet.Subcomplex.homOfLE hAB
  obtain ⟨d, hd⟩ := kan_extension_on_facePoset i a b h
  let f := SubcomplexFaceComparison.map B ≫ d
  have hf : SSet.sd.map i ≫ f = lastVertex.app A.toSSet ≫ a := by
    change SSet.sd.map i ≫ (SubcomplexFaceComparison.map B ≫ d) = _
    rw [← Category.assoc, SubcomplexFaceComparison.map_naturality hAB,
      Category.assoc, hd, ← Category.assoc, SubcomplexFaceComparison.map_lastVertex]
  obtain ⟨e, _, he, _⟩ := exists_simplexSubcomplex_subdivision_relative_descent A B i a f hf
  exact ⟨e, he⟩

/-- Every continuous extension of an actual simplex boundary into a Kan
realization has an exact simplicial extension of that same boundary. -/
theorem kan_extension_of_realization_boundary_extension {X : SSet.{0}}
    [SSet.KanComplex X] (n : ℕ) (a : (SSet.boundary n : SSet.{0}) ⟶ X)
    (b : SSet.toTop.obj (Δ[n] : SSet.{0}) ⟶ SSet.toTop.obj X)
    (h : SSet.toTop.map (SSet.boundary n).ι ≫ b = SSet.toTop.map a) :
    ∃ d : (Δ[n] : SSet.{0}) ⟶ X, (SSet.boundary n).ι ≫ d = a := by
  let T : (Δ[n] : SSet.{0}).Subcomplex := ⊤
  let e := SSet.Subcomplex.topIso (Δ[n] : SSet.{0})
  let i : (SSet.boundary n : SSet.{0}) ⟶ T.toSSet := SSet.Subcomplex.homOfLE le_top
  have hi : i ≫ e.hom = (SSet.boundary n).ι := rfl
  have hb : SSet.toTop.map i ≫ (SSet.toTop.map e.hom ≫ b) = SSet.toTop.map a := by
    rw [← Category.assoc, ← SSet.toTop.map_comp, hi, h]
  obtain ⟨d, hd⟩ := kan_extension_of_subcomplex_realization_extension
    (SSet.boundary n) T le_top a (SSet.toTop.map e.hom ≫ b) hb
  refine ⟨e.inv ≫ d, ?_⟩
  rw [← hi]
  exact (Category.assoc _ _ _).trans
    ((congrArg (i ≫ ·) (e.hom_inv_id_assoc d)).trans hd)

end

end Thomason.Construction

end

section

/-! # Acyclic Kan boundary lifting over a standard simplex

The continuous fibre extension gives an exact
simplicial fibre extension. This discharges all dimensions of boundary
lifting over an actual standard simplex, using actual realization W.
-/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem acyclic_kan_simplex_boundary_lifting {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ (Δ[m] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) : HasLiftingProperty (SSet.boundary n).ι p := by
  apply simplex_boundary_lifting_of_initial_fiber m n p
  intro a
  let v := initialSimplexVertex m
  let F := simplicialPointFiber p v
  let : SSet.KanComplex F.toSSet := simplicialPointFiber_kan p v
  obtain ⟨S, _, a', c, ha', hc⟩ := finite_relative_simplex_fiber_extension m p hp v
    (SSet.boundary n).ι a
  apply kan_extension_of_realization_boundary_extension n a
    (c ≫ SSet.toTop.map S.ι)
  rw [← Category.assoc, hc, ← SSet.toTop.map_comp, ha']

theorem acyclic_kan_simplex_boundary_rlp {E : SSet.{0}} (m : ℕ)
    (p : E ⟶ (Δ[m] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) : I.rlp p := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact acyclic_kan_simplex_boundary_lifting m n p hp

end

end Thomason.Construction

end

end OAI
