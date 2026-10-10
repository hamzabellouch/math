import Mathlib

namespace OAI

section


/-! Literal continuous gluing on locally finite closed covers. This is used for
cell-by-cell homotopies; it does not assume cell extensions exist. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.ClosedCoverGluing
variable {J X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (S : J → Set X) (φ : ∀ j, C(S j,Y))
  (agree : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), φ i ⟨x,hi⟩ = φ j ⟨x,hj⟩)
  (cover : ⋃ j, S j = Set.univ) (closed : ∀ j, IsClosed (S j))
  (finite : LocallyFinite S)

/-- Gluing is with the actual source topology, not a replacement quotient. -/
def glue : C(X,Y) where
  toFun := Set.liftCover S (fun j => φ j) agree cover
  continuous_toFun := by
    apply finite.continuous cover closed
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (S j).domRestrict (Set.liftCover S (fun j => φ j) agree cover) = φ j := by
      funext x
      exact Set.liftCover_coe x
    rw [he]
    exact (φ j).continuous

@[simp] lemma glue_apply (j : J) (x : S j) :
    glue S φ agree cover closed finite x = φ j x := by
  change Set.liftCover S (fun j => φ j) agree cover x = φ j x
  exact Set.liftCover_coe x

lemma glue_eq (j : J) (x : X) (hx : x ∈ S j) :
    glue S φ agree cover closed finite x = φ j ⟨x,hx⟩ :=
  glue_apply S φ agree cover closed finite j ⟨x,hx⟩

/-- A homotopy prescribed continuously on each closed cell glues once the
literal formulas coincide on intersections. -/
def gluePrism (H : ∀ j, C(I × S j,Y))
    (ha : ∀ i j (t : I) x (hi : x ∈ S i) (hj : x ∈ S j),
      H i (t,⟨x,hi⟩) = H j (t,⟨x,hj⟩)) : C(I × X,Y) := by
  let T : J → Set (I × X) := fun j => Prod.snd ⁻¹' S j
  let ψ : ∀ j, C(T j,Y) := fun j =>
    { toFun tx := H j (tx.val.1,⟨tx.val.2,tx.property⟩)
      continuous_toFun := (H j).continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)) }
  have ht : ⋃ j, T j = Set.univ := by
    ext tx
    simpa only [Set.mem_iUnion,Set.mem_preimage,T,Set.mem_univ,iff_true] using
      Set.iUnion_eq_univ_iff.mp cover tx.2
  have hf : LocallyFinite T := finite.preimage_continuous continuous_snd
  exact glue T ψ (fun i j tx hi hj => ha i j tx.1 tx.2 hi hj) ht
    (fun j => (closed j).preimage continuous_snd) hf

lemma gluePrism_apply (H : ∀ j, C(I × S j,Y))
    (ha : ∀ i j (t : I) x (hi : x ∈ S i) (hj : x ∈ S j),
      H i (t,⟨x,hi⟩) = H j (t,⟨x,hj⟩)) (j : J) (t : I) (x : S j) :
    gluePrism S cover closed finite H ha (t,x) = H j (t,x) := by
  dsimp only [gluePrism]
  exact glue_eq _ _ _ _ _ _ j (t,(x : X)) x.property

end HyperbolicObstruction.ClosedCoverGluing
end
end

section

end

end OAI
