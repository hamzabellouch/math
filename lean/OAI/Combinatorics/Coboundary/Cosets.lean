import OAI.Combinatorics.Coboundary.Cones

namespace OAI

noncomputable section

/-!
Typed coset complexes, their links, face models, and connectedness from generation.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.TypedCosetFaces
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)
abbrev Vertex := (i : I) × G ⧸ H i
instance : DecidableEq (Vertex H) := Classical.decEq _
def vertex (g : G) (i : I) : Vertex H := ⟨i, QuotientGroup.mk g⟩
def face (g : G) (A : Finset I) : Finset (Vertex H) := A.image (vertex H g)
def types (σ : Finset (Vertex H)) : Finset I := σ.image Sigma.fst
def IsFace (σ : Finset (Vertex H)) : Prop := ∃ g A, face H g A = σ
def stabilizer (A : Finset I) : Subgroup G := ⨅ i ∈ A, H i

omit [DecidableEq I] in
@[simp] theorem mem_stabilizer (A : Finset I) (g : G) :
    g ∈ stabilizer H A ↔ ∀ i ∈ A, g ∈ H i := by simp [stabilizer]

omit [DecidableEq I] in
lemma vertex_injective (g : G) : Function.Injective (vertex H g) := by
  intro i j hij
  exact congrArg Sigma.fst hij

omit [DecidableEq I] in
@[simp] theorem face_card (g : G) (A : Finset I) : (face H g A).card = A.card :=
  Finset.card_image_of_injective _ (vertex_injective H g)

@[simp] theorem types_face (g : G) (A : Finset I) : types H (face H g A) = A := by
  simp [types, face, Finset.image_image, vertex, Function.comp_def]

omit [DecidableEq I] in
@[simp] lemma vertex_mem (g h : G) (i : I) (A : Finset I) :
    vertex H g i ∈ face H h A ↔ i ∈ A ∧ (QuotientGroup.mk g : G ⧸ H i) = QuotientGroup.mk h := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    have hji : j = i := congrArg Sigma.fst he
    subst j
    exact ⟨hj, (eq_of_heq (Sigma.mk.inj_iff.mp he).2).symm⟩
  · rintro ⟨hi,he⟩
    apply Finset.mem_image.mpr
    exact ⟨i, hi, by simp [vertex, he]⟩

omit [DecidableEq I] in
lemma face_eq_iff (g h : G) (A : Finset I) :
    face H g A = face H h A ↔ g⁻¹*h ∈ stabilizer H A := by
  rw [mem_stabilizer]
  constructor
  · intro he i hi
    have hm : vertex H g i ∈ face H h A := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact ((vertex_mem H g h i A).mp hm).2)
  · intro he
    apply Finset.ext
    intro x
    rcases x with ⟨i,x⟩
    induction x using Quotient.inductionOn with | h x =>
      change vertex H x i ∈ face H g A ↔ vertex H x i ∈ face H h A
      rw [vertex_mem, vertex_mem]
      by_cases hi : i ∈ A
      · have hg : (QuotientGroup.mk g : G ⧸ H i) = QuotientGroup.mk h :=
          Quotient.sound (QuotientGroup.leftRel_apply.mpr (he i hi))
        rw [hg]
      · simp [hi]

abbrev FaceOfType (A : Finset I) := {σ : Finset (Vertex H) // IsFace H σ ∧ types H σ = A}

def quotientFace (A : Finset I) : G ⧸ stabilizer H A → FaceOfType H A :=
  Quotient.lift (fun g => ⟨face H g A, ⟨g,A,rfl⟩, types_face H g A⟩) (by
    intro g h he
    apply Subtype.ext
    exact (face_eq_iff H g h A).mpr (QuotientGroup.leftRel_apply.mp he))

lemma quotientFace_bijective (A : Finset I) : Function.Bijective (quotientFace H A) := by
  constructor
  · intro a b he
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    exact (face_eq_iff H a b A).mp (congrArg Subtype.val he)
  · rintro ⟨σ,hσ,hA⟩
    obtain ⟨g,B,rfl⟩ := hσ
    have hBA : B = A := by simpa using hA
    subst B
    exact ⟨QuotientGroup.mk g,rfl⟩

def faceEquiv (A : Finset I) : G ⧸ stabilizer H A ≃ FaceOfType H A :=
  Equiv.ofBijective (quotientFace H A) (quotientFace_bijective H A)

@[simp] lemma faceEquiv_mk (A : Finset I) (g : G) :
    (faceEquiv H A (QuotientGroup.mk g)).val = face H g A := rfl

end CoboundaryExpanders.TypedCosetFaces

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.TypedCosetFaces

section
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

abbrev Remaining (A : Finset I) := {i : I // i ∉ A}

def linkGroups (A : Finset I) (j : Remaining A) : Subgroup (stabilizer H A) :=
  (H j.val).comap (stabilizer H A).subtype

def linkVertex (A : Finset I) : Vertex (linkGroups H A) → Vertex H :=
  fun x => ⟨x.1.val,Quotient.lift (fun g : stabilizer H A =>
    (QuotientGroup.mk g.val : G ⧸ H x.1.val)) (by
      intro g h he
      apply Quotient.sound
      have hh : g⁻¹*h ∈ linkGroups H A x.1 := QuotientGroup.leftRel_apply.mp he
      exact QuotientGroup.leftRel_apply.mpr hh) x.2⟩

omit [DecidableEq I] in
@[simp] lemma linkVertex_vertex (A : Finset I) (g : stabilizer H A) (j : Remaining A) :
    linkVertex H A (vertex (linkGroups H A) g j) = vertex H g.val j.val := rfl

omit [DecidableEq I] in
lemma linkVertex_injective (A : Finset I) : Function.Injective (linkVertex H A) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have hij : i = j := Subtype.ext (congrArg Sigma.fst he)
  subst j
  congr 1
  induction x using Quotient.inductionOn with | h x =>
  induction y using Quotient.inductionOn with | h y =>
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  have hq := (Sigma.mk.inj_iff.mp he).2
  have hh := QuotientGroup.leftRel_apply.mp (Quotient.exact (eq_of_heq hq))
  exact hh

omit [DecidableEq I] in
lemma linkVertex_type_not_mem (A : Finset I) (v : Vertex (linkGroups H A)) :
    (linkVertex H A v).1 ∉ A := v.1.property

@[simp] lemma linkFace_image (A : Finset I) (g : stabilizer H A) (B : Finset (Remaining A)) :
    (face (linkGroups H A) g B).image (linkVertex H A) = face H g.val (B.image Subtype.val) := by
  simp only [face,Finset.image_image,Function.comp_def,linkVertex_vertex]

def IsLinkFace (A : Finset I) (s : Finset (Vertex H)) : Prop :=
  Disjoint s (face H 1 A) ∧ IsFace H (s ∪ face H 1 A)

lemma types_of_mem {s : Finset (Vertex H)} {v : Vertex H} (hv : v ∈ s) :
    v.1 ∈ types H s := Finset.mem_image.mpr ⟨v,hv,rfl⟩

omit [DecidableEq I] in
lemma face_subset_iff (g h : G) (A B : Finset I) :
    face H g A ⊆ face H h B ↔ A ⊆ B ∧ ∀ i ∈ A,
      (QuotientGroup.mk g : G ⧸ H i) = QuotientGroup.mk h := by
  constructor
  · intro hs
    have hh i hi := (vertex_mem H g h i B).mp (hs (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    exact ⟨fun i hi => (hh i hi).1,fun i hi => (hh i hi).2⟩
  · rintro ⟨hAB,hgh⟩ v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact (vertex_mem H g h i B).mpr ⟨hAB hi,hgh i hi⟩

theorem isLinkFace_iff (A : Finset I) (s : Finset (Vertex H)) :
    IsLinkFace H A s ↔ ∃ g : stabilizer H A, ∃ B : Finset (Remaining A),
      (face (linkGroups H A) g B).image (linkVertex H A) = s := by
  classical
  constructor
  · rintro ⟨hdis,g,C,hgC⟩
    have hAs : face H 1 A ⊆ face H g C := by rw [hgC]; exact Finset.subset_union_right
    obtain ⟨hAC,hAg⟩ := (face_subset_iff H 1 g A C).mp hAs
    have hg : g ∈ stabilizer H A := by
      rw [mem_stabilizer]
      intro i hi
      have hh := QuotientGroup.leftRel_apply.mp (Quotient.exact (hAg i hi))
      simpa only [inv_one,one_mul] using hh
    let gg : stabilizer H A := ⟨g,hg⟩
    let B : Finset (Remaining A) := (C \ A).subtype (fun i => i ∉ A)
    have hB : B.image Subtype.val = C \ A := by
      ext i
      simp only [B,Finset.mem_image,Finset.mem_subtype,Finset.mem_sdiff]
      constructor
      · rintro ⟨j,hj,rfl⟩; exact hj
      · intro hi; exact ⟨⟨i,hi.2⟩,hi,rfl⟩
    refine ⟨gg,B,?_⟩
    rw [linkFace_image,hB]
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      have his := Finset.mem_sdiff.mp hi
      have hm : vertex H g i ∈ s ∪ face H 1 A := by
        rw [← hgC]; exact Finset.mem_image.mpr ⟨i,his.1,rfl⟩
      rcases Finset.mem_union.mp hm with hm | hm
      · exact hm
      · exact False.elim (his.2 ((vertex_mem H g 1 i A).mp hm).1)
    · intro hv
      have hvc : v ∈ face H g C := by rw [hgC]; exact Finset.mem_union_left _ hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvc
      have hiA : i ∉ A := by
        intro hiA
        have hmm : vertex H g i ∈ face H 1 A :=
          (vertex_mem H g 1 i A).mpr ⟨hiA,(hAg i hiA).symm⟩
        exact Finset.disjoint_left.mp hdis hv hmm
      exact Finset.mem_image.mpr ⟨i,Finset.mem_sdiff.mpr ⟨hi,hiA⟩,rfl⟩
  · rintro ⟨g,B,rfl⟩
    rw [linkFace_image]
    have hA : face H g.val A = face H 1 A := by
      apply (face_eq_iff H g.val 1 A).mpr
      simpa only [mul_one] using (stabilizer H A).inv_mem g.property
    constructor
    · apply Finset.disjoint_left.mpr
      intro v hv hvA
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact j.property ((vertex_mem H g.val 1 j.val A).mp hvA).1
    · refine ⟨g.val,B.image Subtype.val ∪ A,?_⟩
      rw [face,Finset.image_union]
      change face H g.val (B.image Subtype.val) ∪ face H g.val A = _
      rw [hA]

theorem linkFace_iff (A : Finset I) (s : Finset (Vertex (linkGroups H A))) :
    IsFace (linkGroups H A) s ↔ IsLinkFace H A (s.image (linkVertex H A)) := by
  rw [isLinkFace_iff]
  constructor
  · rintro ⟨g,B,rfl⟩; exact ⟨g,B,rfl⟩
  · rintro ⟨g,B,he⟩
    exact ⟨g,B,Finset.image_injective (linkVertex_injective H A) he⟩

end

section
variable {G G' I I' : Type} [Group G] [Group G'] [DecidableEq I] [DecidableEq I']
  (H : I → Subgroup G) (H' : I' → Subgroup G')
  (e : G ≃* G') (r : I ≃ I')
  (he : ∀ i g, g ∈ H i ↔ e g ∈ H' (r i))

def isoVertex : Vertex H → Vertex H' := fun x =>
  ⟨r x.1,Quotient.lift (fun g : G => (QuotientGroup.mk (e g) : G' ⧸ H' (r x.1))) (by
    intro g h hh
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    have hm := (he x.1 (g⁻¹*h)).mp (QuotientGroup.leftRel_apply.mp hh)
    simpa using hm) x.2⟩

omit [DecidableEq I] [DecidableEq I'] in
@[simp] lemma isoVertex_vertex (g : G) (i : I) :
    isoVertex H H' e r he (vertex H g i) = vertex H' (e g) (r i) := rfl

omit [DecidableEq I] [DecidableEq I'] in
lemma isoVertex_injective : Function.Injective (isoVertex H H' e r he) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  have hij : i = j := r.injective (congrArg Sigma.fst hxy)
  subst j
  congr 1
  induction x using Quotient.inductionOn with | h x =>
  induction y using Quotient.inductionOn with | h y =>
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  have hh := QuotientGroup.leftRel_apply.mp
    (Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2))
  apply (he i (x⁻¹*y)).mpr
  simpa using hh

omit [DecidableEq I] [DecidableEq I'] in
lemma isoVertex_surjective : Function.Surjective (isoVertex H H' e r he) := by
  rintro ⟨i,q⟩
  induction q using Quotient.inductionOn with | h q =>
  refine ⟨vertex H (e.symm q) (r.symm i),?_⟩
  simp only [isoVertex_vertex,e.apply_symm_apply,r.apply_symm_apply]
  rfl

def vertexEquiv : Vertex H ≃ Vertex H' :=
  Equiv.ofBijective (isoVertex H H' e r he)
    ⟨isoVertex_injective H H' e r he,isoVertex_surjective H H' e r he⟩

omit [DecidableEq I] in
@[simp] lemma isoFace_image (g : G) (A : Finset I) :
    (face H g A).image (isoVertex H H' e r he) = face H' (e g) (A.image r) := by
  simp only [face,Finset.image_image,Function.comp_def,isoVertex_vertex]

theorem isoFace_iff (s : Finset (Vertex H)) :
    IsFace H' (s.image (isoVertex H H' e r he)) ↔ IsFace H s := by
  constructor
  · rintro ⟨g,A,hg⟩
    refine ⟨e.symm g,A.image r.symm,?_⟩
    apply Finset.image_injective (isoVertex_injective H H' e r he)
    rw [isoFace_image,e.apply_symm_apply]
    have hi : (A.image r.symm).image r = A := by ext i; simp
    rw [hi]
    exact hg
  · rintro ⟨g,A,rfl⟩
    exact ⟨e g,A.image r,(isoFace_image H H' e r he g A).symm⟩

end

section
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def vertexLinkGroups (i : I) (j : {j : I // j ≠ i}) : Subgroup (H i) :=
  (H j.val).comap (H i).subtype

def singleStabilizerEquiv (i : I) : H i ≃* stabilizer H {i} :=
  MulEquiv.subgroupCongr (by ext g; simp [mem_stabilizer])

def singleTypesEquiv (i : I) : {j : I // j ≠ i} ≃ Remaining ({i} : Finset I) :=
  Equiv.subtypeEquivRight (fun j => by simp)

omit [DecidableEq I] in
lemma singletonGroups_correspond (i : I) (j : {j : I // j ≠ i}) (g : H i) :
    g ∈ vertexLinkGroups H i j ↔ singleStabilizerEquiv H i g ∈
      linkGroups H {i} (singleTypesEquiv i j) := Iff.rfl

def vertexLinkEmbedding (i : I) : Vertex (vertexLinkGroups H i) → Vertex H :=
  (linkVertex H {i}) ∘ isoVertex (vertexLinkGroups H i) (linkGroups H {i})
    (singleStabilizerEquiv H i) (singleTypesEquiv i) (singletonGroups_correspond H i)

omit [DecidableEq I] in
lemma vertexLinkEmbedding_injective (i : I) : Function.Injective (vertexLinkEmbedding H i) :=
  (linkVertex_injective H {i}).comp (isoVertex_injective _ _ _ _ _)

omit [DecidableEq I] in
@[simp] lemma vertexLinkEmbedding_vertex (i : I) (g : H i) (j : {j : I // j ≠ i}) :
    vertexLinkEmbedding H i (vertex (vertexLinkGroups H i) g j) = vertex H g.val j.val := rfl

theorem vertexLinkFace_iff (i : I) (s : Finset (Vertex (vertexLinkGroups H i))) :
    IsFace (vertexLinkGroups H i) s ↔ IsLinkFace H {i} (s.image (vertexLinkEmbedding H i)) := by
  unfold vertexLinkEmbedding
  rw [← Finset.image_image,← linkFace_iff,isoFace_iff]

lemma vertexLinkFace_surjective (i : I) (s : Finset (Vertex H)) (hs : IsLinkFace H {i} s) :
    ∃ t : Finset (Vertex (vertexLinkGroups H i)), IsFace (vertexLinkGroups H i) t ∧
      t.image (vertexLinkEmbedding H i) = s := by
  obtain ⟨g,A,hg⟩ := (isLinkFace_iff H {i} s).mp hs
  let e := singleStabilizerEquiv H i
  let r := singleTypesEquiv i
  refine ⟨face _ (e.symm g) (A.image r.symm),⟨_,_,rfl⟩,?_⟩
  unfold vertexLinkEmbedding
  rw [← Finset.image_image,isoFace_image,e.apply_symm_apply]
  have hi : (A.image r.symm).image r = A := by
    rw [Finset.image_image]
    have hcomp : (r ∘ r.symm) = id := by funext x; exact r.apply_symm_apply x
    rw [hcomp,Finset.image_id]
  rw [hi]
  exact hg

end

open InfiniteChains InfiniteChains.Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma subset_face {s : Finset (Vertex H)} {g : G} {A : Finset I} (hs : s ⊆ face H g A) :
    face H g (types H s) = s := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp (hs hw)
    have hj' : j = i := by simpa only [←hje,vertex] using he
    subst j
    simpa only [hje] using hw
  · intro v hv
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (hs hv)
    apply Finset.mem_image.mpr
    refine ⟨i,?_,he⟩
    exact Finset.mem_image.mpr ⟨v,hv,by rw [←he]; rfl⟩

lemma IsFace.downward {s t : Finset (Vertex H)} (hs : IsFace H s) (ht : t ⊆ s) : IsFace H t := by
  obtain ⟨g,A,rfl⟩ := hs
  exact ⟨g,types H t,subset_face H ht⟩

def complex : CoboundaryExpanders.InfiniteChains.Complex (Vertex H) where
  faces := {s | IsFace H s}
  empty_mem := ⟨1,∅,Finset.image_empty _⟩
  downward := fun hs ht => hs.downward H ht

def linkComplex (A : Finset I) : CoboundaryExpanders.InfiniteChains.Complex (Vertex H) where
  faces := {s | IsLinkFace H A s}
  empty_mem := ⟨Finset.disjoint_empty_left _,by simpa only [Finset.empty_union] using (show IsFace H (face H 1 A) from ⟨1,A,rfl⟩)⟩
  downward := by
    intro s t hs ht
    refine ⟨Finset.disjoint_left.mpr ?_,hs.2.downward H (Finset.union_subset_union ht (Finset.Subset.refl _))⟩
    intro v hv hv'
    exact Finset.disjoint_left.mp hs.1 (ht hv) hv'

end CoboundaryExpanders.TypedCosetFaces

end

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains InfiniteChains.Cone
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma vertexPath_common (g : G) (i j : I) :
    VertexPath (complex H) (vertex H g i) (vertex H g j) := by
  apply Relation.ReflTransGen.single
  exact ⟨g,{i,j},by simp [face]⟩

lemma vertexPath_symm {x y : Vertex H} (h : VertexPath (complex H) x y) :
    VertexPath (complex H) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
    exact (Relation.ReflTransGen.single (by simpa only [Finset.pair_comm] using hxy)).trans ih

lemma vertexPath_mul (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (base : I) (x : G) :
    ∀ g, VertexPath (complex H) (vertex H g base) (vertex H (g*x) base) := by
  have hx : x ∈ Subgroup.closure (⋃ i, (H i : Set G)) := by rw [hgen]; trivial
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    intro g
    have he : vertex H g i = vertex H (g*x) i := by
      apply Sigma.mk.inj_iff.mpr
      refine ⟨rfl,heq_of_eq ?_⟩
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simpa using hi))
    have hleft := vertexPath_common H g base i
    have hright := vertexPath_common H (g*x) i base
    rw [←he] at hright
    exact hleft.trans hright
  | one => intro g; simpa only [mul_one,VertexPath] using (Relation.ReflTransGen.refl : VertexPath (complex H) (vertex H g base) _)
  | mul x y hx hy ihx ihy => intro g; simpa only [mul_assoc,VertexPath] using (ihx g).trans (ihy (g*x))
  | inv x hx ih =>
    intro g
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using vertexPath_symm H (ih (g*x⁻¹))

lemma vertexPath_of_generate (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤)
    (base : I) (x y : Vertex H) : VertexPath (complex H) x y := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  induction x using Quotient.inductionOn with | h g =>
    induction y using Quotient.inductionOn with | h h =>
      change VertexPath (complex H) (vertex H g i) (vertex H h j)
      have hd := vertexPath_mul H hgen base (g⁻¹*h) g
      simp only [←mul_assoc,mul_inv_cancel,one_mul] at hd
      exact (vertexPath_common H g i base).trans (hd.trans (vertexPath_common H h base j))

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
