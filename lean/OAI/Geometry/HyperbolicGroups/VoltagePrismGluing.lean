import Mathlib
import OAI.Geometry.HyperbolicGroups.SmallSimplexCoordinates
import OAI.Geometry.HyperbolicGroups.VoltageCellGluing

namespace OAI

/-! A genuine dimension-two contraction gluing theorem. Its local input is a
continuous prism for each face, compatible with the SAME edge prisms. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G)

lemma faceLift_sheet_injective {s : Finset V} (hs : s ∈ K.faces) {a : V} (ha : a ∈ s)
    (g k : G) (x y : closedFace (K := K) s)
    (he : v.faceLift hs ha g x = v.faceLift hs ha k y) : g = k ∧ x = y := by
  have hxy : x = y := Subtype.ext (congrArg v.proj he)
  subst y
  have h1 := congrArg Prod.snd (v.faceLift_chart hs ha ha g x)
  have h2 := congrArg Prod.snd (v.faceLift_chart hs ha ha k x)
  rw [he] at h1
  exact ⟨by simpa [v.self] using h1.symm.trans h2,rfl⟩

lemma edgeLift_exists {a b : V} (h : {a,b} ∈ K.faces) (e : v.TotalSpace)
    (he : v.proj e ∈ closedFace {a,b}) : ∃ g r, v.edgeLift h g r = e := by
  let x : closedFace (K := K) {a,b} := ⟨v.proj e,he⟩
  let g := v.coordinate e * (v.value a (v.core.indexAt (v.proj e)))⁻¹
  refine ⟨g,edgeParameter x,?_⟩
  have hp : edgePath K h (edgeParameter x) = v.proj e :=
    congrArg Subtype.val (edgePoint_parameter h x)
  rw [v.edgeLift_apply,hp]
  apply v.totalSpace_ext
  · rfl
  · simp [inChart_coordinate,g,mul_assoc]

lemma intersection_edge {s t : Finset V} (hs : s ∈ K.faces) (_ : t ∈ K.faces)
    (hsc : s.card ≤ 3) (htc : t.card ≤ 3) (hne : s ≠ t) (e : v.TotalSpace)
    (hx : v.proj e ∈ closedFace s) (hy : v.proj e ∈ closedFace t) :
    ∃ (a b : V) (h : {a,b} ∈ K.faces) (g : G) (r : I), v.edgeLift h g r = e := by
  have hxy := closedFace_inter (v.proj e) hx hy
  obtain ⟨a,b,hab⟩ := nonempty_pair_of_card_le_two
    (closedFace_nonempty (⟨v.proj e,hxy⟩ : closedFace (K := K) (s ∩ t)))
    (inter_card_le_two hsc htc hne)
  have he : {a,b} ∈ K.faces :=
    (K.isRelLowerSet_faces hs).2 (by rw [←hab]; exact Finset.inter_subset_left) (by simp)
  rw [hab] at hxy
  obtain ⟨g,r,hr⟩ := v.edgeLift_exists he e hxy
  exact ⟨a,b,he,g,r,hr⟩

variable (z : v.TotalSpace)
structure EdgePrisms where
  H : ∀ {a b : V}, {a,b} ∈ K.faces → G → C(I × I,v.TotalSpace)
  initial : ∀ {a b} (h : {a,b} ∈ K.faces) g r, H h g (0,r) = v.edgeLift h g r
  final : ∀ {a b} (h : {a,b} ∈ K.faces) g r, H h g (1,r) = z
  agree : ∀ {a b c d} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces) g k t r s,
    v.edgeLift h g r = v.edgeLift h' k s → H h g (t,r) = H h' k (t,s)

variable (E : v.EdgePrisms z)
structure FacePrism (s : Finset V) (hs : s ∈ K.faces) where
  anchor : V
  mem_anchor : anchor ∈ s
  H : G → C(I × closedFace (K := K) s,v.TotalSpace)
  initial : ∀ g x, H g (0,x) = v.faceLift hs mem_anchor g x
  final : ∀ g x, H g (1,x) = z
  edge : ∀ {a b} (he : {a,b} ∈ K.faces) g k t r x,
    v.faceLift hs mem_anchor g x = v.edgeLift he k r → H g (t,x) = E.H he k (t,r)

variable (F : ∀ (s : Finset V) (hs : s ∈ K.faces), v.FacePrism z E s hs)

def anchoredFacePrism (q : FaceAnchor (K := K) × G) :
    C(I × closedFace (K := K) q.1.val.1,v.TotalSpace) :=
  (F q.1.val.1 q.1.property.1).H
    (q.2 * v.value q.1.val.2 (F q.1.val.1 q.1.property.1).anchor)

lemma anchoredFacePrism_lift (q : FaceAnchor (K := K) × G)
    (x : closedFace (K := K) q.1.val.1) :
    v.faceLift q.1.property.1 (F q.1.val.1 q.1.property.1).mem_anchor
      (q.2 * v.value q.1.val.2 (F q.1.val.1 q.1.property.1).anchor) x =
      v.faceLift q.1.property.1 q.1.property.2 q.2 x :=
  v.inChart_change_face q.1.property.1 q.1.property.2
    (F q.1.val.1 q.1.property.1).mem_anchor x q.2

variable (hd : ∀ s ∈ K.faces, s.card ≤ 3)
include hd in
lemma anchoredFacePrism_agree (i j : FaceAnchor (K := K) × G) (t : I)
    (x : closedFace (K := K) i.1.val.1) (y : closedFace (K := K) j.1.val.1)
    (he : v.faceLift i.1.property.1 i.1.property.2 i.2 x =
      v.faceLift j.1.property.1 j.1.property.2 j.2 y) :
    v.anchoredFacePrism z E F i (t,x) = v.anchoredFacePrism z E F j (t,y) := by
  have hh := (v.anchoredFacePrism_lift z E F i x).trans
    (he.trans (v.anchoredFacePrism_lift z E F j y).symm)
  by_cases hst : i.1.val.1 = j.1.val.1
  · rcases i with ⟨⟨⟨s,a⟩,hs,ha⟩,g⟩
    rcases j with ⟨⟨⟨s',b⟩,hs',hb⟩,k⟩
    dsimp at hst
    subst s'
    obtain ⟨hg,hxy⟩ := v.faceLift_sheet_injective hs (F s hs).mem_anchor _ _ x y hh
    change (F s hs).H _ (t,x) = (F s hs).H _ (t,y)
    rw [hg,hxy]
  · let e := v.faceLift i.1.property.1 i.1.property.2 i.2 x
    have hy : v.proj e ∈ closedFace j.1.val.1 := by
      change v.proj (v.faceLift i.1.property.1 i.1.property.2 i.2 x) ∈ _
      rw [he]; exact y.property
    obtain ⟨a,b,h,g,r,hr⟩ := v.intersection_edge i.1.property.1 j.1.property.1
      (hd _ i.1.property.1) (hd _ j.1.property.1) hst e x.property hy
    change (F _ _).H _ (t,x) = (F _ _).H _ (t,y)
    rw [(F _ _).edge h _ g t r x ((v.anchoredFacePrism_lift z E F i x).trans hr.symm),
      (F _ _).edge h _ g t r y ((v.anchoredFacePrism_lift z E F j y).trans (he.symm.trans hr.symm))]

def contraction : C(I × v.TotalSpace,v.TotalSpace) :=
  v.glueFaceHomotopies (v.anchoredFacePrism z E F) (v.anchoredFacePrism_agree z E F hd)

lemma contraction_initial (e : v.TotalSpace) : v.contraction z E F hd (0,e) = e := by
  apply v.glueFaceHomotopies_endpoint
  intro q x
  exact ((F _ _).initial _ x).trans (v.anchoredFacePrism_lift z E F q x)
lemma contraction_final (e : v.TotalSpace) : v.contraction z E F hd (1,e) = z := by
  apply v.glueFaceHomotopies_endpoint (f := fun _ => z)
  intro q x
  exact (F _ _).final _ x

lemma contraction_edge {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t r : I) :
    v.contraction z E F hd (t,v.edgeLift h g r) = E.H h g (t,r) := by
  let q : FaceAnchor (K := K) × G := (⟨({a,b},a),h,by simp⟩,g)
  change v.glueFaceHomotopies _ _ (t,v.faceLift h (a := a) (by simp) g (edgePoint h r)) = _
  rw [v.glueFaceHomotopies_apply (q := q)]
  exact (F _ _).edge h _ g t r (edgePoint h r)
    (v.anchoredFacePrism_lift z E F q (edgePoint h r))

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
