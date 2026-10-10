import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Nonempty
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TopologyTreeSteps

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ} {w v : ClosedLine h ℓ}

def vertexIndex (w : ClosedLine h ℓ) (x : ℤ) : Fin (ℓ+1) :=
  if hx : x ∈ treeVertices w then Classical.choose (mem_image.mp hx) else 0

lemma vertexIndex_spec (w : ClosedLine h ℓ) (x : ℤ) (hx : x ∈ treeVertices w) :
    w.offset (vertexIndex w x)=x := by
  simpa only [vertexIndex,dite_eq_left hx] using (Classical.choose_spec (mem_image.mp hx)).2

lemma offset_mem_vertices (w : ClosedLine h ℓ) (i : Fin (ℓ+1)) :
    w.offset i ∈ treeVertices w := mem_image.mpr ⟨i,mem_univ _,rfl⟩

lemma edgeVertices_subset_vertices (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) :
    edgeVertices w E ⊆ treeVertices w := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hx
    exact offset_mem_vertices w _
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hx
    exact offset_mem_vertices w _

namespace SameGeometry

def vertexImage (_ : SameGeometry w v) (x : ℤ) : ℤ := v.offset (vertexIndex w x)

lemma vertexImage_offset (H : SameGeometry w v) (i : Fin (ℓ+1)) :
    H.vertexImage (w.offset i) = v.offset i :=
  (H.pattern _ _).mp (vertexIndex_spec w (w.offset i) (offset_mem_vertices w i))

lemma vertexImage_injective (H : SameGeometry w v) :
    Set.InjOn H.vertexImage (treeVertices w) := by
  intro x hx y hy he
  have hh := (H.pattern (vertexIndex w x) (vertexIndex w y)).mpr he
  simpa only [vertexIndex_spec w x hx,vertexIndex_spec w y hy] using hh

lemma vertices_image (H : SameGeometry w v) : (treeVertices w).image H.vertexImage = treeVertices v := by
  simp only [treeVertices,image_image,Function.comp_def,H.vertexImage_offset]

lemma edgeVertices_image (H : SameGeometry w v) (E : Finset (Fin ℓ)) :
    (edgeVertices w E).image H.vertexImage = edgeVertices v E := by
  simp only [edgeVertices,image_union,image_image,Function.comp_def,H.vertexImage_offset]

lemma children_image (H : SameGeometry w v) (x : ℤ) (hx : x ∈ treeVertices w) :
    v.children (H.vertexImage x) = w.children x := by
  have he := H.children (vertexIndex w x)
  simpa only [vertexIndex_spec w x hx,vertexImage] using he.symm

lemma weight (H : SameGeometry w v) {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (p : S.Index) (E : Finset (Fin ℓ)) :
    subtreeUnionWeight w p E = subtreeUnionWeight v p E := by
  unfold subtreeUnionWeight
  congr 1
  rw [← H.edgeVertices_image E,prod_image (H.vertexImage_injective.mono (edgeVertices_subset_vertices w E))]
  apply prod_congr rfl
  intro x hx
  rw [H.children_image x (edgeVertices_subset_vertices w E hx)]

lemma modifiedWeight (H : SameGeometry w v) {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (p : S.Index) (E : Finset (Fin ℓ)) :
    OrdinaryCorrelations.GraphKernel.PrimeSystem.modifiedWeight w p E =
      OrdinaryCorrelations.GraphKernel.PrimeSystem.modifiedWeight v p E := by
  simp only [OrdinaryCorrelations.GraphKernel.PrimeSystem.modifiedWeight,H.weight,H.good]

lemma bandDefect (H : SameGeometry w v) (β : ℝ) :
    OrdinaryCorrelations.GraphKernel.PrimeSystem.bandDefect w β =
      OrdinaryCorrelations.GraphKernel.PrimeSystem.bandDefect v β := by
  unfold OrdinaryCorrelations.GraphKernel.PrimeSystem.bandDefect
  rw [← H.vertices_image,sum_image H.vertexImage_injective]
  apply sum_congr rfl
  intro x hx
  rw [H.children_image x hx]

def shapeMap (H : SameGeometry w v) (Q : Shape w) : Shape v where
  top := ⟨v.offset Q.topEdge.castSucc,offset_mem_vertices v _⟩
  edges := ⟨Q.edges.val,mem_erase.mpr ⟨Q.nonempty.ne_empty, (mem_shapes ..).mpr (by
    apply (H.grows Q.topEdge.castSucc Q.edges.val).mp
    simpa only [Q.topEdge_origin] using Q.grows)⟩⟩

lemma shapeMap_edges (H : SameGeometry w v) (Q : Shape w) : (H.shapeMap Q).edges.val=Q.edges.val := rfl

lemma Shape.ext_edges {w : ClosedLine h ℓ} (Q R : Shape w) (hE : Q.edges.val=R.edges.val) : Q=R := by
  have htop : Q.top=R.top := by
    apply Subtype.ext
    rw [← Q.topEdge_origin,← R.topEdge_origin]
    congr 2
    simp only [Shape.topEdge,hE]
  cases Q
  cases R
  cases htop
  congr
  exact Subtype.ext hE

lemma shapeMap_inverse (H : SameGeometry w v) (Q : Shape w) : H.symm.shapeMap (H.shapeMap Q)=Q :=
  Shape.ext_edges _ _ rfl

def shapeEquiv (H : SameGeometry w v) : Shape w ≃ Shape v where
  toFun := H.shapeMap
  invFun := H.symm.shapeMap
  left_inv := H.shapeMap_inverse
  right_inv := H.symm.shapeMap_inverse

lemma goodEdges (H : SameGeometry w v) : OrdinaryCorrelations.NumericalSubtrees.goodEdges w =
    OrdinaryCorrelations.NumericalSubtrees.goodEdges v := by
  ext e
  simp only [OrdinaryCorrelations.NumericalSubtrees.goodEdges,mem_filter,H.trees,H.good]

end SameGeometry

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
