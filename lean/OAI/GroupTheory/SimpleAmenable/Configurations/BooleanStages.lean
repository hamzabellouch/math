import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonDiagramRefinement
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryLabels

namespace OAI

section

section

open Classical Set CategoryTheory
namespace SimpleAmenable.PolygonObject

structure BooleanPartition (a : ℕ) where
  size : ℕ
  color : GenericSquare a → Fin size
  onto : Function.Surjective color
  polygon : ∀ b, {x | color x=b}∈polygonAlgebra a

namespace BooleanPartition
variable {a : ℕ}
noncomputable def cell (P : BooleanPartition a) (b : Fin P.size) : polygonAlgebra a :=
  ⟨_,P.polygon b⟩
noncomputable def point (P : BooleanPartition a) (b : Fin P.size) : GenericSquare a :=
  (P.onto b).choose
@[simp] theorem color_point (P : BooleanPartition a) (b : Fin P.size) :
    P.color (P.point b)=b := (P.onto b).choose_spec

variable {ι : Type} [Fintype ι] (S : ι → polygonAlgebra a)
noncomputable def signature (x : GenericSquare a) : ι → Bool := fun i => decide (x∈(S i).val)

theorem signature_fiber (b : ι → Bool) : {x | signature S x=b}∈polygonAlgebra a := by
  have he : {x | signature S x=b} = ⋂ i, if b i then (S i).val else (S i).valᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    constructor
    · intro h i
      have hx := congrFun h i
      cases hb : b i <;> simp_all [signature]
    · intro h
      funext i
      have hi := h i
      cases hb : b i <;> simp_all [signature]
  rw [he]
  apply BooleanSubalgebra.iInf_mem
  intro i
  split_ifs
  · exact (S i).property
  · exact (polygonAlgebra a).compl_mem (S i).property

noncomputable def generated : BooleanPartition a where
  size := Fintype.card (Set.range (signature S))
  color x := Fintype.equivFin (Set.range (signature S)) ⟨_,⟨x,rfl⟩⟩
  onto b := by
    obtain ⟨x,hx⟩ := ((Fintype.equivFin (Set.range (signature S))).symm b).property
    refine ⟨x,?_⟩
    apply (Equiv.eq_symm_apply _).mp
    exact Subtype.ext hx
  polygon b := by
    convert signature_fiber S (((Fintype.equivFin (Set.range (signature S))).symm b).val) using 1
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← Equiv.eq_symm_apply,Subtype.ext_iff]

theorem generated_constant {x y : GenericSquare a}
    (h : (generated S).color x=(generated S).color y) (i : ι) :
    x∈(S i).val ↔ y∈(S i).val := by
  have h' := congrArg (fun z : Set.range (signature S) => z.val)
    ((Fintype.equivFin (Set.range (signature S))).injective h)
  have hi := congrFun h' i
  by_cases hx : x∈(S i).val <;> by_cases hy : y∈(S i).val <;> simp_all [signature]

theorem exists_common (S : ι → polygonAlgebra a) :
    ∃ P : BooleanPartition a, ∀ i x y, P.color x=P.color y →
      (x∈(S i).val ↔ y∈(S i).val) :=
  ⟨generated S,fun i _ _ h => generated_constant S h i⟩

end BooleanPartition
end SimpleAmenable.PolygonObject

end

section

open Classical Set CategoryTheory
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ}

noncomputable def forget : Labelled a n ⥤ PolygonObject a where
  obj U := U.polygon
  map f := f.arrow

@[simp] lemma inv_arrow {U V : Labelled a n} (f : U ⟶ V) :
    (inv f).arrow=inv f.arrow := (forget (a:=a) (n:=n)).map_inv f

def ObjectUniform (P : BooleanPartition a) (U : Labelled a n) : Prop :=
  ∀ j x y, P.color x=P.color y → (x∈(U.polygon.cell j).val ↔ y∈(U.polygon.cell j).val)

def ArrowUniform (P : BooleanPartition a) {U V : Labelled a n} (f : U ⟶ V) : Prop :=
  ∀ x y, x.val.1=y.val.1 → P.color x.val.2=P.color y.val.2 →
    (f.arrow.toEquiv x).val.1=(f.arrow.toEquiv y).val.1

lemma arrowUniform_id (P : BooleanPartition a) (U : Labelled a n) :
    ArrowUniform P (𝟙 U) := fun _ _ h _ => h

lemma arrowUniform_comp (P : BooleanPartition a) {U V W : Labelled a n}
    {f : U ⟶ V} {g : V ⟶ W} (hf : ArrowUniform P f) (hg : ArrowUniform P g) :
    ArrowUniform P (f≫g) := by
  intro x y h hP
  apply hg
  · exact hf x y h hP
  · rw [f.positional x,f.positional y]
    exact hP

lemma arrowUniform_inv (P : BooleanPartition a) {U V : Labelled a n}
    (hU : ObjectUniform P U) {f : U ⟶ V} (hf : ArrowUniform P f) :
    ArrowUniform P (inv f) := by
  intro x y h hP
  let x' := (inv f).arrow.toEquiv x
  let y' := (inv f).arrow.toEquiv y
  have hx : x'.val.2=x.val.2 := (inv f).positional x
  have hy : y'.val.2=y.val.2 := (inv f).positional y
  have hmem : y.val.2∈(U.polygon.cell x'.val.1).val :=
    (hU x'.val.1 x'.val.2 y.val.2 (by rw [hx]; exact hP)).mp x'.property
  let z : U.polygon.Point := ⟨(x'.val.1,y.val.2),hmem⟩
  have htrack : (f.arrow.toEquiv z).val.1=y.val.1 := by
    have h' := hf z x' rfl (by simp only [z,hx]; exact hP.symm)
    rw [show f.arrow.toEquiv x'=x from by
      dsimp only [x']; rw [inv_arrow,inv_arrow_apply,Equiv.apply_symm_apply]] at h'
    exact h'.trans h
  have hz : f.arrow.toEquiv z=y := by
    apply Subtype.ext
    exact Prod.ext htrack (f.positional z)
  have he : z=y' := by
    apply f.arrow.toEquiv.injective
    rw [hz]
    dsimp only [y']; rw [inv_arrow,inv_arrow_apply,Equiv.apply_symm_apply]
  change x'.val.1=y'.val.1
  have ht := congrArg (fun w : U.polygon.Point => w.val.1) he
  exact ht

variable {κ τ : Type} [Fintype κ] [Fintype τ]
    (U : κ → Labelled a n) (src dst : τ → κ) (f : ∀t,U (src t) ⟶ U (dst t))

theorem exists_uniform_partition :
    ∃ P : BooleanPartition a, (∀ k,ObjectUniform P (U k)) ∧
      (∀ t,ArrowUniform P (f t)) := by
  let I := (Σ k,Fin (U k).polygon.tracks) ⊕
    (Σ t,Fin (U (src t)).polygon.tracks × Fin (U (dst t)).polygon.tracks)
  let S : I → polygonAlgebra a := Sum.elim
    (fun kj => (U kj.1).polygon.cell kj.2)
    (fun tij => ⟨{x | ∃hx : x∈((U (src tij.1)).polygon.cell tij.2.1).val,
      ((f tij.1).arrow.toEquiv ⟨(tij.2.1,x),hx⟩).val.1=tij.2.2},
      targetTrack_fiber_polygon (f tij.1).arrow tij.2.1 tij.2.2⟩)
  obtain ⟨P,hP⟩ := BooleanPartition.exists_common S
  refine ⟨P,?_,?_⟩
  · intro k j x y h
    exact hP (.inl ⟨k,j⟩) x y h
  · intro t x y h hxy
    have h' := hP (.inr ⟨t,x.val.1,(f t).arrow.toEquiv x |>.val.1⟩) x.val.2 y.val.2 hxy
    have hx : x.val.2∈(S (.inr ⟨t,x.val.1,(f t).arrow.toEquiv x |>.val.1⟩)).val :=
      ⟨x.property,rfl⟩
    obtain ⟨hy,he⟩ := h'.mp hx
    have hpt : (⟨(x.val.1,y.val.2),hy⟩ : (U (src t)).polygon.Point)=y := by
      apply Subtype.ext
      exact Prod.ext h rfl
    rw [hpt] at he
    exact he.symm

end Labelled
end SimpleAmenable.PolygonObject

end

end

end OAI
