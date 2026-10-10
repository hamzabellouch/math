import OAI.GroupTheory.Congruence.Basic
import OAI.GroupTheory.Congruence.Patterns
import OAI.Combinatorics.Coboundary.Joins

namespace OAI

/-!
Coset-link identifications, product and cut models, and all proper-link cone bounds.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Construction

section
open Patterns MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Pointwise
variable (p n : ℕ) [Fact p.Prime]

def localReducedHom (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    localGroup p n hn cut →* reducedLocalGroup p n hn m cut where
  toFun g := ⟨localQuotientMap p n hn m cut g,
    ⟨⟨g.val,localGroup_le_U p n hn cut g.property⟩,g.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ g h

lemma localReducedHom_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    Function.Surjective (localReducedHom p n hn m cut) := by
  rintro ⟨q,hq⟩
  obtain ⟨g,hg,hgq⟩ := hq
  exact ⟨⟨g.val,hg⟩,Subtype.ext hgq⟩

lemma localQuotient_cross_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut j : Fin (n+1)) (g : localGroup p n hn cut) (h : localGroup p n hn j)
    (he : localQuotientMap p n hn m cut g = localQuotientMap p n hn m j h) :
    g.val = h.val := by
  apply localGroups_reduction_injective p n hn hm cut j g h
  exact congrArg (fun q : Gquot p (n+1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n+1) m) q).val) he

lemma localReducedHom_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    Function.Injective (localReducedHom p n hn m cut) := by
  intro g h he
  apply Subtype.ext
  exact localQuotient_cross_injective p n hn hm cut cut g h (congrArg Subtype.val he)

def localReducedEquiv (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    localGroup p n hn cut ≃* reducedLocalGroup p n hn m cut :=
  MulEquiv.ofBijective (localReducedHom p n hn m cut)
    ⟨localReducedHom_injective p n hn hm cut,localReducedHom_surjective p n hn m cut⟩

lemma localReducedHom_mem_iff (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut j : Fin (n+1)) (g : localGroup p n hn cut) :
    (localReducedHom p n hn m cut g).val ∈ reducedLocalGroup p n hn m j ↔
      g.val ∈ localGroup p n hn j := by
  constructor
  · rintro ⟨b,hb,he⟩
    have he' : localQuotientMap p n hn m j ⟨b.val,hb⟩ =
        localQuotientMap p n hn m cut g := he
    exact (localQuotient_cross_injective p n hn hm j cut ⟨b.val,hb⟩ g he') ▸ hb
  · intro hg
    exact ⟨⟨g.val,localGroup_le_U p n hn j hg⟩,hg,rfl⟩

def reducedFlagEquiv (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    reducedLocalGroup p n hn m cut ≃*
      (stdFlag (ZMod p) (n+1)).unipotentFlagStabilizer :=
  (localReducedEquiv p n hn hm cut).symm.trans (localFlagEquiv p n hn cut)

lemma reducedFlagEquiv_stabilizer (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut j : Fin (n+1)) (q : reducedLocalGroup p n hn m cut) :
    (reducedFlagEquiv p n hn hm cut q).val ∈
      MulAction.stabilizer ((Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p))
        ((oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j).val,by omega⟩) ↔
      q.val ∈ reducedLocalGroup p n hn m j := by
  change (localFlagEquiv p n hn cut ((localReducedEquiv p n hn hm cut).symm q)).val ∈ _ ↔ _
  rw [localFlagEquiv_stabilizer]
  have he : (localReducedHom p n hn m cut ((localReducedEquiv p n hn hm cut).symm q)).val = q.val :=
    congrArg Subtype.val ((localReducedEquiv p n hn hm cut).apply_symm_apply q)
  exact (localReducedHom_mem_iff p n hn hm cut j
    ((localReducedEquiv p n hn hm cut).symm q)).symm.trans (by rw [he])

end

section
open Patterns MatrixOpposition TypedCosetFaces SphericalOpposition.CompleteFlag
open scoped Pointwise
variable (p n : ℕ) [Fact p.Prime]

def quotientLinkGroups (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1))
    (j : {j : Fin (n+1) // j ≠ cut}) : Subgroup (reducedLocalGroup p n hn m cut) :=
  (reducedLocalGroup p n hn m j.val).comap (reducedLocalGroup p n hn m cut).subtype

lemma quotientLinkGroups_correspond (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut : Fin (n+1)) (j : {j : Fin (n+1) // j ≠ cut})
    (q : reducedLocalGroup p n hn m cut) :
    q ∈ quotientLinkGroups p n hn m cut j ↔
      reducedFlagEquiv p n hn hm cut q ∈
        (stdFlag (ZMod p) (n+1)).vertexStabilizers (oppFlag (ZMod p) (n+1))
          (localTypeEquiv cut j) := by
  change q.val ∈ reducedLocalGroup p n hn m j.val ↔
    reducedFlagEquiv p n hn hm cut q ∈ MulAction.stabilizer _
      ((oppFlag (ZMod p) (n+1)).baseSpace (localTypeEquiv cut j))
  have hr : properIndex (N:=n+1) (localTypeEquiv cut j) =
      (⟨n+1-(cutOrder cut j.val).val,by omega⟩ : Fin (n+2)) :=
    Fin.ext (localTypeEquiv_rank cut j)
  rw [baseSpace,hr]
  rw [MulAction.mem_stabilizer_iff]
  change q.val ∈ reducedLocalGroup p n hn m j.val ↔
    (reducedFlagEquiv p n hn hm cut q).val •
      (oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j.val).val,by omega⟩ =
      (oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j.val).val,by omega⟩
  exact (reducedFlagEquiv_stabilizer p n hn hm cut j.val q).symm

def quotientLinkVertexModel (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    Vertex (quotientLinkGroups p n hn m cut) → Submodule (ZMod p) (Fin (n+1) → ZMod p) :=
  ((stdFlag (ZMod p) (n+1)).cosetVertexMap (oppFlag (ZMod p) (n+1))) ∘
    isoVertex (quotientLinkGroups p n hn m cut)
      ((stdFlag (ZMod p) (n+1)).vertexStabilizers (oppFlag (ZMod p) (n+1)))
      (reducedFlagEquiv p n hn hm cut) (localTypeEquiv cut)
      (quotientLinkGroups_correspond p n hn hm cut)

lemma quotientLinkVertexModel_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    Function.Injective (quotientLinkVertexModel p n hn hm cut) :=
  ((stdFlag (ZMod p) (n+1)).cosetVertexMap_injective (oppFlag (ZMod p) (n+1))).comp
    (isoVertex_injective _ _ _ _ _)

theorem quotientLinkFace_iff (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1))
    (s : Finset (Vertex (quotientLinkGroups p n hn m cut))) :
    IsFace (quotientLinkGroups p n hn m cut) s ↔
      s.image (quotientLinkVertexModel p n hn hm cut) ∈
        (stdFlag (ZMod p) (n+1)).complex.faces := by
  unfold quotientLinkVertexModel
  rw [← Finset.image_image,← cosetFace_iff stdFlags_opposite,isoFace_iff]

theorem quotientLinkFace_surjective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1))
    (s : Finset (Submodule (ZMod p) (Fin (n+1) → ZMod p)))
    (hs : s ∈ (stdFlag (ZMod p) (n+1)).complex.faces) :
    ∃ t : Finset (Vertex (quotientLinkGroups p n hn m cut)),
      IsFace (quotientLinkGroups p n hn m cut) t ∧
      t.image (quotientLinkVertexModel p n hn hm cut) = s := by
  obtain ⟨g,A,hg⟩ := opposedFace_coset stdFlags_opposite s hs
  let e := reducedFlagEquiv p n hn hm cut
  let r := localTypeEquiv cut
  refine ⟨face (quotientLinkGroups p n hn m cut) (e.symm g) (A.image r.symm),⟨_,_,rfl⟩,?_⟩
  unfold quotientLinkVertexModel
  rw [← Finset.image_image,isoFace_image,e.apply_symm_apply]
  have hi : (A.image r.symm).image r = A := by ext j; simp
  rw [hi]
  exact hg

def actualLinkEmbedding (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    Vertex (quotientLinkGroups p n hn m cut) → Vertex (reducedLocalGroup p n hn m) :=
  vertexLinkEmbedding (reducedLocalGroup p n hn m) cut

lemma actualLinkEmbedding_injective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    Function.Injective (actualLinkEmbedding p n hn m cut) :=
  vertexLinkEmbedding_injective _ _

theorem actualLinkFace_iff (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1))
    (s : Finset (Vertex (quotientLinkGroups p n hn m cut))) :
    IsLinkFace (reducedLocalGroup p n hn m) {cut}
        (s.image (actualLinkEmbedding p n hn m cut)) ↔
      s.image (quotientLinkVertexModel p n hn hm cut) ∈
        (stdFlag (ZMod p) (n+1)).complex.faces := by
  exact (vertexLinkFace_iff (reducedLocalGroup p n hn m) cut s).symm.trans
    (quotientLinkFace_iff p n hn hm cut s)

lemma actualLinkFace_surjective (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1))
    (s : Finset (Vertex (reducedLocalGroup p n hn m)))
    (hs : IsLinkFace (reducedLocalGroup p n hn m) {cut} s) :
    ∃ t : Finset (Vertex (quotientLinkGroups p n hn m cut)),
      IsFace (quotientLinkGroups p n hn m cut) t ∧
      t.image (actualLinkEmbedding p n hn m cut) = s :=
  vertexLinkFace_surjective _ _ _ hs

end

open InfiniteChains InfiniteChains.Cone TypedCosetFaces SphericalOpposition.CompleteFlag
open Patterns MatrixOpposition
variable (p n : ℕ) [Fact p.Prime]

def sphericalLinkModel (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m) (cut : Fin (n+1)) :
    FaceModel (TypedCosetFaces.complex (quotientLinkGroups p n hn m cut))
      (stdFlag (ZMod p) (n+1)).complex where
  vertex := quotientLinkVertexModel p n hn hm cut
  injective := quotientLinkVertexModel_injective p n hn hm cut
  face_iff := fun s => (quotientLinkFace_iff p n hn hm cut s).symm
  cover := fun t ht => quotientLinkFace_surjective p n hn hm cut t ht

def actualVertexLinkModel (hn : 1 ≤ n) (m : ℕ) (cut : Fin (n+1)) :
    FaceModel (TypedCosetFaces.complex (quotientLinkGroups p n hn m cut))
      (linkComplex (reducedLocalGroup p n hn m) {cut}) where
  vertex := actualLinkEmbedding p n hn m cut
  injective := actualLinkEmbedding_injective p n hn m cut
  face_iff := fun s => (vertexLinkFace_iff (reducedLocalGroup p n hn m) cut s).symm
  cover := fun t ht => actualLinkFace_surjective p n hn m cut t ht

theorem uniform_actual_vertex_cones (n : ℕ) (hn : 1 ≤ n) :
    ∃ Q R : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m → ∀ cut : Fin (n+1),
        Nonempty (BoundedCone (linkComplex (reducedLocalGroup p n hn m) {cut}) (n-1) R) := by
  obtain ⟨Q,R,h⟩ := exists_uniform_cones (n-1)
  refine ⟨Q,R,?_⟩
  intro p hp hq m hm cut
  have hc := h (ZMod p) (Fin (n+1) → ZMod p) (n+1) (stdFlag (ZMod p) (n+1)) (by omega)
    (by simpa only [ZMod.card] using hq)
  exact ⟨(actualVertexLinkModel p n hn m cut).pushCone
    ((sphericalLinkModel p n hn hm cut).pullCone hc.some)⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.InfiniteChains
namespace Complex
variable {V : Type} [DecidableEq V] (X : CoboundaryExpanders.InfiniteChains.Complex V)

def faceLink (s : Finset V) (hs : s ∈ X.faces) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {a | Disjoint s a ∧ s ∪ a ∈ X.faces}
  empty_mem := ⟨Finset.disjoint_empty_right _,by simpa using hs⟩
  downward := by
    intro a b ha hb
    exact ⟨Finset.disjoint_left.mpr (fun v hv hv' => Finset.disjoint_left.mp ha.1 hv (hb hv')),
      X.downward ha.2 (Finset.union_subset_union (Finset.Subset.refl _) hb)⟩

end Complex

open Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

def linkModel (s : Finset V) (hs : s ∈ X.faces) :
    FaceModel (X.faceLink s hs) (Y.faceLink (s.image M.vertex) ((M.face_iff s).mpr hs)) where
  vertex := M.vertex
  injective := M.injective
  face_iff := by
    intro a
    change Disjoint (s.image M.vertex) (a.image M.vertex) ∧
      s.image M.vertex ∪ a.image M.vertex ∈ Y.faces ↔
      Disjoint s a ∧ s ∪ a ∈ X.faces
    rw [←Finset.image_union,M.face_iff,Finset.disjoint_image M.injective]
  cover := by
    intro t ht
    obtain ⟨a,ha,he⟩ := M.cover t (Y.downward ht.2 Finset.subset_union_right)
    refine ⟨a,⟨?_,?_⟩,he⟩
    · rw [←Finset.disjoint_image M.injective,he]
      exact ht.1
    · apply (M.face_iff _).mp
      rw [Finset.image_union,he]
      exact ht.2

end Cone.FaceModel

omit [DecidableEq V] in
lemma complex_eq {X Y : CoboundaryExpanders.InfiniteChains.Complex V} (h : X.faces = Y.faces) : X = Y := by
  cases X; cases Y; cases h; rfl

lemma faceLink_empty (X : CoboundaryExpanders.InfiniteChains.Complex V) : X.faceLink ∅ X.empty_mem = X := by
  apply complex_eq
  ext s
  simp [Complex.faceLink]

lemma faceLink_iterated (X : CoboundaryExpanders.InfiniteChains.Complex V) {s a : Finset V} (hs : s ∈ X.faces)
    (ha : a ∈ (X.faceLink s hs).faces) :
    (X.faceLink s hs).faceLink a ha = X.faceLink (s∪a) ha.2 := by
  apply complex_eq
  ext t
  change (Disjoint a t ∧ Disjoint s (a∪t) ∧ s∪(a∪t) ∈ X.faces) ↔
    (Disjoint (s∪a) t ∧ (s∪a)∪t ∈ X.faces)
  simp only [Finset.disjoint_union_left,Finset.disjoint_union_right,ha.1,true_and,Finset.union_assoc]
  tauto

namespace Join

omit [DecidableEq V] [DecidableEq W] in
lemma mem_link_left {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {s : Finset (W ⊕ V)}
    (hs : s ∈ (complex X Y).faces) : s.toLeft ∈ X.faces := hs.1
omit [DecidableEq V] [DecidableEq W] in
lemma mem_link_right {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {s : Finset (W ⊕ V)}
    (hs : s ∈ (complex X Y).faces) : s.toRight ∈ Y.faces := hs.2

omit [DecidableEq V] [DecidableEq W] in
lemma disjoint_split (s t : Finset (W ⊕ V)) :
    Disjoint s t ↔ Disjoint s.toLeft t.toLeft ∧ Disjoint s.toRight t.toRight := by
  rw [Finset.disjoint_left,Finset.disjoint_left,Finset.disjoint_left]
  constructor
  · intro h
    constructor
    · intro v hv hv'; exact h (by simpa using hv) (by simpa using hv')
    · intro v hv hv'; exact h (by simpa using hv) (by simpa using hv')
  · rintro ⟨hL,hR⟩ (v|v) hv hv'
    · exact hL (by simpa using hv) (by simpa using hv')
    · exact hR (by simpa using hv) (by simpa using hv')

lemma link_eq {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {s : Finset (W ⊕ V)}
    (hs : s ∈ (complex X Y).faces) :
    (complex X Y).faceLink s hs =
      complex (X.faceLink s.toLeft hs.1) (Y.faceLink s.toRight hs.2) := by
  apply complex_eq
  ext t
  change (Disjoint s t ∧ (s∪t).toLeft ∈ X.faces ∧ (s∪t).toRight ∈ Y.faces) ↔
    (Disjoint s.toLeft t.toLeft ∧ s.toLeft∪t.toLeft ∈ X.faces) ∧
      (Disjoint s.toRight t.toRight ∧ s.toRight∪t.toRight ∈ Y.faces)
  rw [disjoint_split,Finset.toLeft_union,Finset.toRight_union]
  tauto

def emptyLeftModel {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V}
    (hX : ∀ s ∈ X.faces, s = ∅) : FaceModel Y (complex X Y) where
  vertex := Sum.inr
  injective := Sum.inr_injective
  face_iff := by
    intro s
    change (s.image Sum.inr).toLeft ∈ X.faces ∧ (s.image Sum.inr).toRight ∈ Y.faces ↔ _
    have hL : (s.image (Sum.inr : V → W ⊕ V)).toLeft = ∅ := by ext a; simp
    have hR : (s.image (Sum.inr : V → W ⊕ V)).toRight = s := by ext a; simp
    rw [hL,hR]
    simp only [X.empty_mem,true_and]
  cover := by
    intro t ht
    refine ⟨t.toRight,ht.2,?_⟩
    have he := Finset.toLeft_disjSum_toRight (u:=t)
    rw [hX t.toLeft ht.1] at he
    rw [Finset.empty_disjSum,Finset.map_eq_image] at he
    exact he

end Join
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
variable {G K I J : Type} [Group G] [Group K] [DecidableEq I] [DecidableEq J]
  (H : I → Subgroup G) (L : J → Subgroup K)

def productGroups : I ⊕ J → Subgroup (G × K)
  | Sum.inl i => (H i).prod ⊤
  | Sum.inr j => (⊤ : Subgroup G).prod (L j)

def productVertex : Vertex (productGroups H L) → Vertex H ⊕ Vertex L
  | ⟨Sum.inl i,q⟩ => Quotient.lift (fun g : G × K => Sum.inl (vertex H g.1 i)) (by
      intro g h hgh
      apply congrArg Sum.inl
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      exact QuotientGroup.leftRel_apply.mpr (QuotientGroup.leftRel_apply.mp hgh).1) q
  | ⟨Sum.inr j,q⟩ => Quotient.lift (fun g : G × K => Sum.inr (vertex L g.2 j)) (by
      intro g h hgh
      apply congrArg Sum.inr
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      exact QuotientGroup.leftRel_apply.mpr (QuotientGroup.leftRel_apply.mp hgh).2) q

omit [DecidableEq I] [DecidableEq J] in
@[simp] lemma productVertex_left (g : G × K) (i : I) :
    productVertex H L (vertex (productGroups H L) g (Sum.inl i)) = Sum.inl (vertex H g.1 i) := rfl
omit [DecidableEq I] [DecidableEq J] in
@[simp] lemma productVertex_right (g : G × K) (j : J) :
    productVertex H L (vertex (productGroups H L) g (Sum.inr j)) = Sum.inr (vertex L g.2 j) := rfl

def embedLeft : Vertex H → Vertex (productGroups H L)
  | ⟨i,q⟩ => Quotient.lift (fun g : G => vertex (productGroups H L) (g,1) (Sum.inl i)) (by
      intro g h hgh
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      exact ⟨QuotientGroup.leftRel_apply.mp hgh,Subgroup.mem_top _⟩) q

def embedRight : Vertex L → Vertex (productGroups H L)
  | ⟨j,q⟩ => Quotient.lift (fun g : K => vertex (productGroups H L) (1,g) (Sum.inr j)) (by
      intro g h hgh
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      exact ⟨Subgroup.mem_top _,QuotientGroup.leftRel_apply.mp hgh⟩) q

def productVertexEquiv : Vertex (productGroups H L) ≃ Vertex H ⊕ Vertex L where
  toFun := productVertex H L
  invFun := Sum.elim (embedLeft H L) (embedRight H L)
  left_inv := by
    rintro ⟨i,q⟩
    cases i with
    | inl i =>
      induction q using Quotient.inductionOn with | h g =>
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change g.1⁻¹*g.1 ∈ H i ∧ _
      simp
    | inr j =>
      induction q using Quotient.inductionOn with | h g =>
      refine Sigma.ext (by rfl) (heq_of_eq ?_)
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change _ ∧ g.2⁻¹*g.2 ∈ L j
      simp
  right_inv := by
    intro x
    cases x with
    | inl x =>
      rcases x with ⟨i,q⟩
      induction q using Quotient.inductionOn with | h g => rfl
    | inr x =>
      rcases x with ⟨j,q⟩
      induction q using Quotient.inductionOn with | h g => rfl

lemma productFace_image (g : G) (k : K) (A : Finset I) (B : Finset J) :
    (face (productGroups H L) (g,k) (A.image Sum.inl ∪ B.image Sum.inr)).image
      (productVertex H L) = (face H g A).image Sum.inl ∪ (face L k B).image Sum.inr := by
  simp only [face,Finset.image_union,Finset.image_image,Function.comp_def,
    productVertex_left,productVertex_right]

lemma productFace_image_general (g : G × K) (A : Finset (I ⊕ J)) :
    ∃ (B : Finset I) (C : Finset J),
      (face (productGroups H L) g A).image (productVertex H L) =
        (face H g.1 B).image Sum.inl ∪ (face L g.2 C).image Sum.inr := by
  refine ⟨A.toLeft,A.toRight,?_⟩
  have he : A.toLeft.image Sum.inl ∪ A.toRight.image Sum.inr = A := by ext x; cases x <;> simp
  calc
    _ = (face (productGroups H L) g (A.toLeft.image Sum.inl ∪ A.toRight.image Sum.inr)).image (productVertex H L) := by rw [he]
    _ = _ := productFace_image H L g.1 g.2 A.toLeft A.toRight

theorem productFace_iff (s : Finset (Vertex (productGroups H L))) :
    IsFace (productGroups H L) s ↔ ∃ (sL : Finset (Vertex H)) (sR : Finset (Vertex L)),
      IsFace H sL ∧ IsFace L sR ∧
      s.image (productVertex H L) = sL.image Sum.inl ∪ sR.image Sum.inr := by
  constructor
  · rintro ⟨g,A,rfl⟩
    obtain ⟨B,C,h⟩ := productFace_image_general H L g A
    exact ⟨face H g.1 B,face L g.2 C,⟨_,_,rfl⟩,⟨_,_,rfl⟩,h⟩
  · rintro ⟨sL,sR,⟨g,A,rfl⟩,⟨k,B,rfl⟩,he⟩
    refine ⟨(g,k),A.image Sum.inl ∪ B.image Sum.inr,?_⟩
    apply Finset.image_injective (productVertexEquiv H L).injective
    exact (productFace_image H L g k A B).trans he.symm

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains.Cone.FaceModel
variable {V W Z : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Z]
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} {T : CoboundaryExpanders.InfiniteChains.Complex Z}
def trans (M : FaceModel X Y) (L : FaceModel Y T) : FaceModel X T where
  vertex := L.vertex ∘ M.vertex
  injective := L.injective.comp M.injective
  face_iff := by intro s; rw [←Finset.image_image,L.face_iff,M.face_iff]
  cover := by
    intro t ht
    obtain ⟨b,hb,he⟩ := L.cover t ht
    obtain ⟨a,ha,hf⟩ := M.cover b hb
    exact ⟨a,ha,by rw [←Finset.image_image,hf,he]⟩
end CoboundaryExpanders.InfiniteChains.Cone.FaceModel

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
variable {G G' I I' : Type} [Group G] [Group G'] [DecidableEq I] [DecidableEq I']
variable (H : I → Subgroup G) (H' : I' → Subgroup G')
variable (e : G ≃* G') (r : I ≃ I') (he : ∀ i g, g ∈ H i ↔ e g ∈ H' (r i))

def isoModel : FaceModel (complex H) (complex H') where
  vertex := isoVertex H H' e r he
  injective := isoVertex_injective H H' e r he
  face_iff := isoFace_iff H H' e r he
  cover := by
    intro t ht
    let a := t.image (vertexEquiv H H' e r he).symm
    have ha : a.image (isoVertex H H' e r he) = t := by
      change a.image (vertexEquiv H H' e r he) = t
      simp only [a,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    exact ⟨a,(isoFace_iff H H' e r he a).mp (by rwa [ha]),ha⟩

variable {K J : Type} [Group K] [DecidableEq J] (L : J → Subgroup K)
def productModel : FaceModel (complex (productGroups H L)) (Join.complex (complex H) (complex L)) where
  vertex := productVertex H L
  injective := (productVertexEquiv H L).injective
  face_iff := by
    intro s
    change IsFace H (s.image (productVertex H L)).toLeft ∧
      IsFace L (s.image (productVertex H L)).toRight ↔ IsFace (productGroups H L) s
    rw [productFace_iff]
    constructor
    · rintro ⟨hL,hR⟩
      refine ⟨_,_,hL,hR,?_⟩
      ext v
      cases v <;> simp
    · rintro ⟨a,b,ha,hb,he⟩
      rw [he]
      have hL : (a.image (Sum.inl : Vertex H → Vertex H ⊕ Vertex L) ∪ b.image Sum.inr).toLeft = a := by ext v; simp
      have hR : (a.image (Sum.inl : Vertex H → Vertex H ⊕ Vertex L) ∪ b.image Sum.inr).toRight = b := by ext v; simp
      exact ⟨by rwa [hL],by rwa [hR]⟩
  cover := by
    intro t ht
    let s := t.image (productVertexEquiv H L).symm
    have he : s.image (productVertex H L) = t := by
      change s.image (productVertexEquiv H L) = t
      simp only [s,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    refine ⟨s,(productFace_iff H L s).mpr ⟨t.toLeft,t.toRight,ht.1,ht.2,?_⟩,he⟩
    rw [he]
    ext v
    cases v <;> simp
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}

instance cutDecidableEq : DecidableEq (Cut N) := Classical.decEq _
instance cutFinite : Finite (Cut N) := Finite.of_injective (fun c : Cut N => (⟨c.val,c.property.2⟩ : Fin N))
  (fun _ _ h => Subtype.ext (congrArg Fin.val h))
noncomputable instance cutFintype : Fintype (Cut N) := Fintype.ofFinite _

def cutTypeEquiv : Cut N ≃ Fin (N-1) where
  toFun c := ⟨N-c.val-1,by have h:=c.property; omega⟩
  invFun i := ⟨N-i.val-1,by have h:=i.isLt; omega⟩
  left_inv c := by apply Subtype.ext; have h:=c.property; dsimp; omega
  right_inv i := by apply Fin.ext; have h:=i.isLt; dsimp; omega

lemma cutGroups_correspond (c : Cut N) (g : upperGroup K N) :
    upperFlagEquiv g ∈ (stdFlag K N).vertexStabilizers (oppFlag K N) (cutTypeEquiv c) ↔
      g ∈ cutGroups K N c := by
  change upperFlagEquiv g • (oppFlag K N).baseSpace (cutTypeEquiv c) = _ ↔ _
  have he : properIndex (N:=N) (cutTypeEquiv c) = (⟨N-c.val,by have h:=c.property; omega⟩:Fin (N+1)) := by
    apply Fin.ext
    have h:=c.property
    dsimp [properIndex,cutTypeEquiv]
    omega
  unfold baseSpace
  rw [he]
  rfl

def cutSphericalModel : FaceModel (TypedCosetFaces.complex (cutGroups K N)) (stdFlag K N).complex :=
  (isoModel (cutGroups K N) ((stdFlag K N).vertexStabilizers (oppFlag K N))
    upperFlagEquiv cutTypeEquiv (fun c g => (cutGroups_correspond c g).symm)).trans
    { vertex := (stdFlag K N).cosetVertexMap (oppFlag K N)
      injective := (stdFlag K N).cosetVertexMap_injective (oppFlag K N)
      face_iff := fun s => (cosetFace_iff stdFlags_opposite s).symm
      cover := fun s hs => by
        obtain ⟨g,A,he⟩ := opposedFace_coset stdFlags_opposite s hs
        exact ⟨_,⟨g,A,rfl⟩,he⟩ }

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma standard_face_mem (A : Finset I) : face H 1 A ∈ (complex H).faces := ⟨1,A,rfl⟩
lemma linkComplex_eq (A : Finset I) : linkComplex H A =
    (complex H).faceLink (face H 1 A) (standard_face_mem H A) := by
  apply InfiniteChains.complex_eq
  ext t
  change Disjoint t (face H 1 A) ∧ IsFace H (t ∪ face H 1 A) ↔
    Disjoint (face H 1 A) t ∧ IsFace H (face H 1 A ∪ t)
  rw [disjoint_comm,Finset.union_comm]

def singleLinkModel (i : I) :
    FaceModel (complex (vertexLinkGroups H i)) (linkComplex H {i}) where
  vertex := vertexLinkEmbedding H i
  injective := vertexLinkEmbedding_injective H i
  face_iff := fun s => (vertexLinkFace_iff H i s).symm
  cover := fun t ht => vertexLinkFace_surjective H i t ht
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
variable {K : Type} [Field K] {a b : ℕ}

def middleCut (ha : 0 < a) (hb : 0 < b) : Cut (a+b) := ⟨a,ha,by omega⟩
def cutLinkTypes (ha : 0 < a) (hb : 0 < b) : Cut a ⊕ Cut b ≃
    {c : Cut (a+b) // c ≠ middleCut ha hb} := cutSplitEquiv.trans
  { toFun := fun c => ⟨c.val,fun h => c.property (congrArg Subtype.val h)⟩
    invFun := fun c => ⟨c.val,fun h => c.property (Subtype.ext h)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma cutLinkGroups_correspond (ha : 0 < a) (hb : 0 < b) (c : Cut a ⊕ Cut b)
    (g : upperGroup K a × upperGroup K b) :
    g ∈ productGroups (cutGroups K a) (cutGroups K b) c ↔
      blockSuffixEquiv g ∈ vertexLinkGroups (cutGroups K (a+b)) (middleCut ha hb) (cutLinkTypes ha hb c) := by
  have h := (blockSuffix_system g c).symm
  cases c with
  | inl c =>
    change (g.1 ∈ cutGroups K a c ∧ True) ↔
      (blockSuffixEquiv g).val ∈ cutGroups K (a+b) (cutSplitEquiv (Sum.inl c)).val
    rw [and_true]
    exact h
  | inr c =>
    change (True ∧ g.2 ∈ cutGroups K b c) ↔
      (blockSuffixEquiv g).val ∈ cutGroups K (a+b) (cutSplitEquiv (Sum.inr c)).val
    rw [true_and]
    exact h

def cutProductLinkModel (ha : 0 < a) (hb : 0 < b) :
    FaceModel (TypedCosetFaces.complex (productGroups (cutGroups K a) (cutGroups K b)))
      (TypedCosetFaces.complex (vertexLinkGroups (cutGroups K (a+b)) (middleCut ha hb))) :=
  isoModel _ _ blockSuffixEquiv (cutLinkTypes ha hb) (cutLinkGroups_correspond ha hb)

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

instance vertexAction : MulAction G (Vertex H) where
  smul g v := ⟨v.1,g • v.2⟩
  one_smul v := by rcases v with ⟨i,v⟩; exact congrArg (Sigma.mk i) (one_smul G v)
  mul_smul g h v := by rcases v with ⟨i,v⟩; exact congrArg (Sigma.mk i) (mul_smul g h v)

omit [DecidableEq I] in
@[simp] lemma smul_vertex (g h : G) (i : I) : g • vertex H h i = vertex H (g*h) i := rfl

omit [DecidableEq I] in
@[simp] lemma smul_face (g h : G) (A : Finset I) : g • face H h A = face H (g*h) A := by
  simp only [Finset.smul_finset_def,face,Finset.image_image,Function.comp_def,smul_vertex]

omit [DecidableEq I] in
lemma IsFace.smul {s : Finset (Vertex H)} (hs : IsFace H s) (g : G) : IsFace H (g • s) := by
  obtain ⟨h,A,rfl⟩ := hs
  rw [smul_face]
  exact ⟨g*h,A,rfl⟩

lemma IsFace.type_card {s : Finset (Vertex H)} (hs : IsFace H s) : (types H s).card = s.card := by
  obtain ⟨g,A,rfl⟩ := hs
  rw [types_face,face_card]

omit [DecidableEq I] in
lemma coset_pure [Fintype I] :
    (∃ t, IsFace H t ∧ t.card = Fintype.card I) ∧
      ∀ s, IsFace H s → ∃ t, IsFace H t ∧ t.card = Fintype.card I ∧ s ⊆ t := by
  constructor
  · exact ⟨face H 1 Finset.univ,⟨1,_,rfl⟩,by simp⟩
  · rintro s ⟨g,A,rfl⟩
    exact ⟨face H g Finset.univ,⟨g,_,rfl⟩,by simp,Finset.image_mono _ (Finset.subset_univ _)⟩

omit [DecidableEq I] in
lemma chamber_transitive [Fintype I] {s t : Finset (Vertex H)}
    (hs : IsFace H s) (ht : IsFace H t) (hsc : s.card = Fintype.card I) (htc : t.card = Fintype.card I) :
    ∃ g : G, g • s = t := by
  obtain ⟨g,A,rfl⟩ := hs
  obtain ⟨h,B,rfl⟩ := ht
  have ha : A = Finset.univ := Finset.eq_univ_of_card A (by simpa using hsc)
  have hb : B = Finset.univ := Finset.eq_univ_of_card B (by simpa using htc)
  subst A; subst B
  exact ⟨h*g⁻¹,by simp [mul_assoc]⟩

omit [DecidableEq I] in
lemma stabilizer_fixes (A : Finset I) (g : stabilizer H A) :
    (g.val : G) • face H 1 A = face H 1 A := by
  rw [smul_face,mul_one]
  apply (face_eq_iff H _ _ _).mpr
  simp

lemma remaining_card [Fintype I] (A : Finset I) :
    Fintype.card (Remaining A) = Fintype.card I - A.card := by
  simpa only [Remaining,Fintype.card_coe] using Fintype.card_subtype_compl (fun i : I => i ∈ A)

omit [DecidableEq I] in
lemma linkFace_smul (A : Finset I) {s : Finset (Vertex H)} (hs : IsLinkFace H A s)
    (g : stabilizer H A) : IsLinkFace H A (g.val • s) := by
  constructor
  · rw [←stabilizer_fixes H A g]
    simp only [Finset.smul_finset_def]
    exact (Finset.disjoint_image (f:=fun v : Vertex H => (g.val:G) • v)
      (MulAction.injective (β:=Vertex H) (g.val:G))).mpr hs.1
  · have hh := hs.2.smul H g.val
    simpa only [Finset.smul_finset_union,stabilizer_fixes H A g] using hh

lemma link_chamber_transitive [Fintype I] (A : Finset I) {s t : Finset (Vertex H)}
    (hs : IsLinkFace H A s) (ht : IsLinkFace H A t)
    (hsc : s.card = Fintype.card I - A.card) (htc : t.card = Fintype.card I - A.card) :
    ∃ g : stabilizer H A, g.val • s = t := by
  obtain ⟨g,B,hg⟩ := (isLinkFace_iff H A s).mp hs
  obtain ⟨h,C,hh⟩ := (isLinkFace_iff H A t).mp ht
  have hB : B = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [remaining_card]
    rw [←hg,Finset.card_image_of_injective _ (linkVertex_injective H A),face_card] at hsc
    exact hsc
  have hC : C = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [remaining_card]
    rw [←hh,Finset.card_image_of_injective _ (linkVertex_injective H A),face_card] at htc
    exact htc
  subst B; subst C
  refine ⟨h*g⁻¹,?_⟩
  rw [←hg,←hh,linkFace_image,linkFace_image,smul_face]
  congr 1
  simp

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains

section
open Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Cone.BoundedCone
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ}
def weaken (H : BoundedCone X n R) {m S : ℕ} (hm : m ≤ n) (hS : R ≤ S) : BoundedCone X m S where
  hom := H.hom
  support := fun s hs hn => H.support s hs (hn.trans hm)
  contraction := fun s hs hn => H.contraction s hs (hn.trans hm)
  bound := fun s hs hn => (H.bound s hs (hn.trans hm)).trans hS
end Cone.BoundedCone

def RankBound (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) : Prop := ∀ s ∈ X.faces, s.card ≤ N

def AllLinkCones (X : CoboundaryExpanders.InfiniteChains.Complex V) (N R : ℕ) : Prop :=
  ∀ s : Finset V, ∀ hs : s ∈ X.faces, s.card < N →
    Nonempty (BoundedCone (X.faceLink s hs) (N-s.card-1) R)

lemma RankBound.link {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hX : RankBound X N)
    {s : Finset V} (hs : s ∈ X.faces) : RankBound (X.faceLink s hs) (N-s.card) := by
  intro a ha
  have h := hX (s∪a) ha.2
  rw [Finset.card_union_of_disjoint ha.1] at h
  omega

lemma RankBound.terminal {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hX : RankBound X N)
    {s : Finset V} (hs : s ∈ X.faces) (hN : s.card = N) :
    ∀ a ∈ (X.faceLink s hs).faces, a = ∅ := by
  intro a ha
  have h := hX.link hs a ha
  rw [hN,Nat.sub_self] at h
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)

lemma AllLinkCones.weaken {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R S : ℕ} (h : AllLinkCones X N R) (hS : R ≤ S) :
    AllLinkCones X N S := by
  intro s hs hn
  exact ⟨(h s hs hn).some.weaken le_rfl hS⟩

lemma Cone.FaceModel.pushAllLinks {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N R : ℕ} (h : AllLinkCones X N R) : AllLinkCones Y N R := by
  intro t ht hn
  obtain ⟨s,hs,rfl⟩ := M.cover t ht
  rw [Finset.card_image_of_injective _ M.injective] at hn ⊢
  exact ⟨(M.linkModel s hs).pushCone (h s hs hn).some⟩

lemma Cone.FaceModel.pullAllLinks {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N R : ℕ} (h : AllLinkCones Y N R) : AllLinkCones X N R := by
  intro s hs hn
  have hc : (s.image M.vertex).card < N := by rwa [Finset.card_image_of_injective _ M.injective]
  have H := h (s.image M.vertex) ((M.face_iff s).mpr hs) hc
  rw [Finset.card_image_of_injective _ M.injective] at H
  exact ⟨(M.linkModel s hs).pullCone H.some⟩

omit [DecidableEq V] in
lemma Cone.FaceModel.rankBound {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N : ℕ} (h : RankBound X N) : RankBound Y N := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := M.cover t ht
  rw [Finset.card_image_of_injective _ M.injective]
  exact h s hs

namespace Join

def emptyRightModel {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V}
    (hY : ∀ s ∈ Y.faces, s = ∅) : FaceModel X (complex X Y) where
  vertex := Sum.inl
  injective := Sum.inl_injective
  face_iff := by
    intro s
    change (s.image Sum.inl).toLeft ∈ X.faces ∧ (s.image Sum.inl).toRight ∈ Y.faces ↔ _
    have hL : (s.image (Sum.inl : W → W ⊕ V)).toLeft = s := by ext a; simp
    have hR : (s.image (Sum.inl : W → W ⊕ V)).toRight = ∅ := by ext a; simp
    rw [hL,hR]
    simp only [Y.empty_mem,and_true]
  cover := by
    intro t ht
    refine ⟨t.toLeft,ht.1,?_⟩
    have he := Finset.toLeft_disjSum_toRight (u:=t)
    rw [hY t.toRight ht.2,Finset.disjSum_empty,Finset.map_eq_image] at he
    exact he

omit [DecidableEq V] [DecidableEq W] in
lemma rankBound {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {A B : ℕ}
    (hX : RankBound X A) (hY : RankBound Y B) : RankBound (complex X Y) (A+B) := by
  intro s hs
  have hL := hX s.toLeft hs.1
  have hR := hY s.toRight hs.2
  have hC := Finset.card_toLeft_add_card_toRight (u:=s)
  omega

theorem allLinkCones {X : CoboundaryExpanders.InfiniteChains.Complex W} {Y : CoboundaryExpanders.InfiniteChains.Complex V} {A B R S : ℕ}
    (hX : RankBound X A) (hY : RankBound Y B)
    (hCX : AllLinkCones X A R) (hCY : AllLinkCones Y B S) :
    AllLinkCones (complex X Y) (A+B) (R+S+(1+R*(A+1))*S) := by
  intro s hs hn
  have hL := hX s.toLeft hs.1
  have hR := hY s.toRight hs.2
  have hC := Finset.card_toLeft_add_card_toRight (u:=s)
  rw [link_eq hs]
  by_cases hA : s.toLeft.card = A
  · have hB : s.toRight.card < B := by omega
    have he : A+B-s.card-1 = B-s.toRight.card-1 := by omega
    rw [he]
    exact ⟨((emptyLeftModel (hX.terminal hs.1 hA)).pushCone (hCY _ hs.2 hB).some).weaken le_rfl (by omega)⟩
  by_cases hB : s.toRight.card = B
  · have hAl : s.toLeft.card < A := by omega
    have he : A+B-s.card-1 = A-s.toLeft.card-1 := by omega
    rw [he]
    exact ⟨((emptyRightModel (hY.terminal hs.2 hB)).pushCone (hCX _ hs.1 hAl).some).weaken le_rfl (by omega)⟩
  have hAl : s.toLeft.card < A := by omega
  have hBl : s.toRight.card < B := by omega
  have he : A+B-s.card-1 = (A-s.toLeft.card-1)+(B-s.toRight.card-1)+1 := by omega
  rw [he]
  refine ⟨(boundedCone (hCX _ hs.1 hAl).some (hCY _ hs.2 hBl).some).weaken le_rfl ?_⟩
  apply max_le
  · omega
  · have hh := Nat.mul_le_mul_right S (Nat.add_le_add_left
      (Nat.mul_le_mul_left R (show A-s.toLeft.card-1+1 ≤ A+1 by omega)) 1)
    omega

end Join
end

open Cone
variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
lemma singleton_mem_of_mem_face {X : CoboundaryExpanders.InfiniteChains.Complex V} {s : Finset V} (hs : s ∈ X.faces)
    {v : V} (hv : v ∈ s) : {v} ∈ X.faces := X.downward hs (Finset.singleton_subset_iff.mpr hv)

lemma faceLink_congr {X : CoboundaryExpanders.InfiniteChains.Complex V} {s t : Finset V} (hs : s ∈ X.faces) (ht : t ∈ X.faces)
    (h : s = t) : X.faceLink s hs = X.faceLink t ht := by subst t; rfl

lemma AllLinkCones.vertexCriterion {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R : ℕ} (hN : 0 < N)
    (hBase : Nonempty (BoundedCone X (N-1) R))
    (hVertex : ∀ v : V, ∀ hv : {v} ∈ X.faces,
      AllLinkCones (X.faceLink {v} hv) (N-1) R) : AllLinkCones X N R := by
  intro s hs hn
  by_cases he : s = ∅
  · subst s
    simpa only [faceLink_empty,Finset.card_empty,Nat.sub_zero] using hBase
  obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hvx := singleton_mem_of_mem_face hs hv
  have hu : {v} ∪ s.erase v = s := by simp [Finset.insert_erase hv]
  have ht : s.erase v ∈ (X.faceLink {v} hvx).faces := by
    constructor
    · simp
    · rwa [hu]
  have hc : (s.erase v).card = s.card-1 := Finset.card_erase_of_mem hv
  have hlt : (s.erase v).card < N-1 := by have hp := Finset.card_pos.mpr ⟨v,hv⟩; omega
  have H := hVertex v hvx (s.erase v) ht hlt
  rw [faceLink_iterated,faceLink_congr ht.2 hs hu] at H
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  have he : (N-1)-(s.erase v).card-1 = N-s.card-1 := by omega
  rwa [he] at H

end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def actionModel (g : G) : FaceModel (complex H) (complex H) where
  vertex := fun v => g • v
  injective := MulAction.injective g
  face_iff := by
    intro s
    change IsFace H (g • s) ↔ IsFace H s
    constructor
    · intro h
      have hh := h.smul H g⁻¹
      have he : g⁻¹ • (g • s) = s := inv_smul_smul g s
      rw [he] at hh
      exact hh
    · exact fun h => h.smul H g
  cover := by
    intro t ht
    refine ⟨g⁻¹ • t,ht.smul H g⁻¹,?_⟩
    change g • (g⁻¹ • t) = t
    exact smul_inv_smul g t

lemma rankBound [Fintype I] : InfiniteChains.RankBound (complex H) (Fintype.card I) := by
  rintro s ⟨g,A,rfl⟩
  rw [face_card]
  exact Finset.card_le_univ _

lemma standard_singleton_face (i : I) : {vertex H 1 i} ∈ (complex H).faces := by
  exact ⟨1,{i},by simp [face]⟩
lemma standard_link_eq (i : I) : linkComplex H {i} =
    (complex H).faceLink {vertex H 1 i} (standard_singleton_face H i) := by
  simpa only [face,Finset.image_singleton] using linkComplex_eq H {i}

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}

lemma card_cut (N : ℕ) : Fintype.card (Cut N) = N-1 := by
  rw [Fintype.card_congr (cutTypeEquiv (N:=N)),Fintype.card_fin]
lemma cut_rankBound : RankBound (TypedCosetFaces.complex (cutGroups K N)) (N-1) := by
  simpa only [card_cut] using TypedCosetFaces.rankBound (cutGroups K N)

lemma cut_middle_link_cones {a b R S : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hA : AllLinkCones (TypedCosetFaces.complex (cutGroups K a)) (a-1) R)
    (hB : AllLinkCones (TypedCosetFaces.complex (cutGroups K b)) (b-1) S) :
    AllLinkCones (linkComplex (cutGroups K (a+b)) {middleCut ha hb})
      ((a-1)+(b-1)) (R+S+(1+R*((a-1)+1))*S) := by
  have hj := Join.allLinkCones cut_rankBound cut_rankBound hA hB
  exact (singleLinkModel _ _).pushAllLinks
    ((cutProductLinkModel ha hb).pushAllLinks
      ((productModel (cutGroups K a) (cutGroups K b)).pullAllLinks hj))

theorem uniform_cut_allLinkCones (N : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K], Q < Fintype.card K →
      AllLinkCones (TypedCosetFaces.complex (cutGroups K N)) (N-1) R := by
  classical
  induction N using Nat.strong_induction_on with | h N ih =>
  by_cases hN : N ≤ 1
  · exact ⟨0,0,fun _ _ _ _ s _ hs => by omega⟩
  have hN2 : 2 ≤ N := by omega
  obtain ⟨Q0,R0,h0⟩ := exists_uniform_cones (N-2)
  choose q r hr using fun i : Fin N => ih i.val i.isLt
  let QL := ∑ i : Fin N, q i
  let L := ∑ i : Fin N, r i
  let B := L+L+(1+L*(N+1))*L
  refine ⟨max Q0 QL,max R0 B,?_⟩
  intro K _ _ hQ
  have hsmall (a : ℕ) (ha : a < N) :
      AllLinkCones (TypedCosetFaces.complex (cutGroups K a)) (a-1) L := by
    have hq : q ⟨a,ha⟩ ≤ QL := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have hr' : r ⟨a,ha⟩ ≤ L := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    exact (hr ⟨a,ha⟩ K (lt_of_le_of_lt (hq.trans (le_max_right _ _)) hQ)).weaken hr'
  apply AllLinkCones.vertexCriterion (by omega : 0 < N-1)
  · have H := h0 K (Fin N → K) N (stdFlag K N) (by omega)
      (lt_of_le_of_lt (le_max_left _ _) hQ)
    have hh := cutSphericalModel (K:=K) (N:=N) |>.pullCone H.some
    have he : N-1-1 = N-2 := by omega
    rw [he]
    exact ⟨hh.weaken le_rfl (le_max_left _ _)⟩
  intro v hv
  rcases v with ⟨c,v⟩
  induction v using Quotient.inductionOn with | h g =>
  have hstandard : AllLinkCones (linkComplex (cutGroups K N) {c}) (N-1-1) (max R0 B) := by
    rcases c with ⟨a,ha,haN⟩
    obtain ⟨b,hNb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt haN)
    subst N
    have hb : 0 < b := by omega
    have hbN : b < a+b := by omega
    have hc := cut_middle_link_cones ha hb (hsmall a haN) (hsmall b hbN)
    have he : (a-1)+(b-1) = a+b-1-1 := by omega
    rw [he] at hc
    refine hc.weaken ?_
    apply le_trans _ (le_max_right _ _)
    dsimp [B]
    gcongr
    omega
  rw [standard_link_eq] at hstandard
  have hm := (actionModel (cutGroups K N) g).linkModel {vertex (cutGroups K N) 1 c}
    (standard_singleton_face _ _)
  have hh := hm.pushAllLinks hstandard
  have he : (actionModel (cutGroups K N) g).vertex (vertex (cutGroups K N) 1 c) =
      vertex (cutGroups K N) g c := by
    change g • vertex (cutGroups K N) 1 c = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex (cutGroups K N) 1 c} : Finset _).image
      (actionModel (cutGroups K N) g).vertex = {vertex (cutGroups K N) g c} := by
    rw [Finset.image_singleton,he]
  rw [faceLink_congr _ hv hi] at hh
  exact hh

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.InfiniteChains
open Cone
variable {V : Type} [DecidableEq V]

def ProperLinkCones (X : CoboundaryExpanders.InfiniteChains.Complex V) (N R : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∀ hs : s ∈ X.faces, s.card < N →
    Nonempty (BoundedCone (X.faceLink s hs) (N-s.card-1) R)

lemma ProperLinkCones.vertexCriterion {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R : ℕ}
    (hVertex : ∀ v : V, ∀ hv : {v} ∈ X.faces,
      AllLinkCones (X.faceLink {v} hv) (N-1) R) : ProperLinkCones X N R := by
  intro s hne hs hn
  obtain ⟨v,hv⟩ := hne
  have hvx := singleton_mem_of_mem_face hs hv
  have hu : {v} ∪ s.erase v = s := by simp [Finset.insert_erase hv]
  have ht : s.erase v ∈ (X.faceLink {v} hvx).faces := by
    constructor
    · simp
    · rwa [hu]
  have hc : (s.erase v).card = s.card-1 := Finset.card_erase_of_mem hv
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  have hlt : (s.erase v).card < N-1 := by omega
  have H := hVertex v hvx (s.erase v) ht hlt
  rw [faceLink_iterated,faceLink_congr ht.2 hs hu] at H
  have he : (N-1)-(s.erase v).card-1 = N-s.card-1 := by omega
  rwa [he] at H
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma allVertexLinks_of_standard {N R : ℕ}
    (hs : ∀ i : I, AllLinkCones (linkComplex H {i}) N R) :
    ∀ v : Vertex H, ∀ hv : {v} ∈ (complex H).faces,
      AllLinkCones ((complex H).faceLink {v} hv) N R := by
  rintro ⟨i,v⟩ hv
  induction v using Quotient.inductionOn with | h g =>
  have hh := hs i
  rw [standard_link_eq] at hh
  have hh' := ((actionModel H g).linkModel {vertex H 1 i} (standard_singleton_face H i)).pushAllLinks hh
  have he : (actionModel H g).vertex (vertex H 1 i) = vertex H g i := by
    change g • vertex H 1 i = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex H 1 i} : Finset _).image (actionModel H g).vertex = {vertex H g i} := by
    rw [Finset.image_singleton,he]
  rw [faceLink_congr _ hv hi] at hh'
  exact hh'
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone TypedCosetFaces SphericalOpposition.CompleteFlag MatrixOpposition

theorem uniform_actual_proper_link_cones (n : ℕ) (hn : 1 ≤ n) :
    ∃ Q R : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p →
      ∀ m : ℕ, 2 ≤ m →
        ProperLinkCones (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) R := by
  obtain ⟨Q,R,h⟩ := uniform_cut_allLinkCones (n+1)
  refine ⟨Q,R,?_⟩
  intro p hp hq m hm
  have hspherical := (cutSphericalModel (K:=ZMod p) (N:=n+1)).pushAllLinks
    (h (ZMod p) (by simpa only [ZMod.card] using hq))
  have hspherical' : AllLinkCones (stdFlag (ZMod p) (n+1)).complex n R := by
    simpa only [Nat.add_sub_cancel] using hspherical
  apply ProperLinkCones.vertexCriterion
  apply allVertexLinks_of_standard
  intro cut
  have hc := (sphericalLinkModel p n hn hm cut).pullAllLinks hspherical'
  have ha := (actualVertexLinkModel p n hn m cut).pushAllLinks hc
  simpa only [Nat.add_sub_cancel] using ha

end CoboundaryExpanders.Construction

end

end OAI
