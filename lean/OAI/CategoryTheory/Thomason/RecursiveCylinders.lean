import Mathlib
import OAI.CategoryTheory.Thomason.GrayGenerators

namespace OAI

/-! Recursive Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def projectionIndex (i : Fin 23) : ℕ × Bool :=
  ![(0,false), (1,true), (2,false), (1,false), (0,false), (1,true),
    (1,true), (2,false), (1,false), (2,false), (2,false), (2,false),
    (1,false), (1,true), (2,false), (1,false), (0,true), (0,true),
    (0,false), (1,true), (2,false), (1,false), (0,true)] i

lemma pastedObj_projection {X : OmegaCategory.{v}} (L R : Diagram X)
    (a b : X.Cell) (ha : X.source 2 a = a) (hb : X.source 2 b = b)
    (hab : X.target 0 a = X.source 0 b)
    (hL : ∀ i, L.obj i = X.face (projectionIndex i).1 (projectionIndex i).2 a)
    (hR : ∀ i, R.obj i = X.face (projectionIndex i).1 (projectionIndex i).2 b)
    (i : Fin 7) : pastedObj L R (generators i) =
      X.face (projectionIndex (generators i)).1 (projectionIndex (generators i)).2 (X.join 0 a b) := by
  fin_cases i
  · change X.join 0 (L.obj 2) (R.obj 2) = X.source 2 (X.join 0 a b)
    rw [hL, hR]
    change X.join 0 (X.source 2 a) (X.source 2 b) = _
    exact (X.join_source_gt 2 0 a b (by decide) hab).symm
  · change L.obj 4 = X.source 0 (X.join 0 a b)
    rw [hL]
    change X.source 0 a = _
    exact (X.join_source_le 0 0 a b le_rfl hab).symm
  · change X.join 1 (X.join 0 (L.obj 6) (R.obj 19))
      (X.join 0 (L.obj 1) (R.obj 6)) = X.target 1 (X.join 0 a b)
    rw [hL, hR, hL, hR]
    change X.join 1 (X.join 0 (X.target 1 a) (X.target 1 b))
      (X.join 0 (X.target 1 a) (X.target 1 b)) = _
    rw [← X.join_target_gt 1 0 a b (by decide) hab]
    exact X.join_left_unit 1 _ _ (X.source_target_self 1 _) (by
      rw [X.target_target_self, X.source_target_self])
  · change X.join 1 (X.join 0 (L.obj 10) (R.obj 21))
      (X.join 0 (L.obj 1) (R.obj 10)) = X.source 2 (X.join 0 a b)
    rw [hL, hR, hL, hR]
    change X.join 1 (X.join 0 (X.source 2 a) (X.source 1 b))
      (X.join 0 (X.target 1 a) (X.source 2 b)) = _
    rw [X.join_source_gt 2 0 a b (by decide) hab, ha, hb]
    exact (X.join_factor_right 0 1 (by decide) a b hab).symm
  · change X.join 1 (X.join 0 (L.obj 12) (R.obj 21))
      (X.join 0 (L.obj 3) (R.obj 12)) = X.source 1 (X.join 0 a b)
    rw [hL, hR, hL, hR]
    change X.join 1 (X.join 0 (X.source 1 a) (X.source 1 b))
      (X.join 0 (X.source 1 a) (X.source 1 b)) = _
    rw [← X.join_source_gt 1 0 a b (by decide) hab]
    exact X.join_left_unit 1 _ _ (X.source_source_self 1 _) (by
      rw [X.target_source_self, X.source_source_self])
  · change R.obj 17 = X.target 0 (X.join 0 a b)
    rw [hR]
    change X.target 0 b = _
    exact (X.join_target_le 0 0 a b le_rfl hab).symm
  · change X.join 0 (L.obj 20) (R.obj 20) = X.source 2 (X.join 0 a b)
    rw [hL, hR]
    change X.join 0 (X.source 2 a) (X.source 2 b) = _
    exact (X.join_source_gt 2 0 a b (by decide) hab).symm

end Thomason.GrayTwo

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex GrayComposition OmegaCategory

lemma endpoint_top (b : Bool) :
    (endpoint.{u} 2 b).map (topTable 2) = cell.{u} (if b then 20 else 2) := by
  apply coordinates_injective
  rw [coordinates_cell]
  revert b
  decide

lemma tensorFace_vertical (b : Bool) :
    (tensorFace.{u} 2 0 b).map (verticalTable (topTable 0)) =
      cell.{u} (if b then 17 else 4) := by
  rw [tensorFace, verticalTable_natural, faceMap_top]
  apply coordinates_injective
  rw [coordinates_cell]
  revert b
  decide

lemma pushout_glue :
    (j₀.{u} 2 0).map (cell.{u} 17) = (j₁.{u} 2 0).map (cell.{u} 4) := by
  have h := congrArg (fun f : T.{u} 0 ⟶ Q.{u} 2 0 => f.map (verticalTable (topTable 0)))
    (pushout.condition (f := tensorFace.{u} 2 0 true) (g := tensorFace.{u} 2 0 false))
  change (j₀.{u} 2 0).map ((tensorFace.{u} 2 0 true).map (verticalTable (topTable 0))) =
    (j₁.{u} 2 0).map ((tensorFace.{u} 2 0 false).map (verticalTable (topTable 0))) at h
  simpa only [tensorFace_vertical, ite_true, Bool.false_eq_true, ite_false] using h

def cooperation : T.{u} 2 ⟶ Q.{u} 2 0 :=
  (paste (diagramOfFunctor (j₀.{u} 2 0)) (diagramOfFunctor (j₁.{u} 2 0)) pushout_glue).lift

lemma cooperation_cell (i : Fin 23) :
    cooperation.map (cell.{u} i) =
      pastedObj (diagramOfFunctor (j₀.{u} 2 0)) (diagramOfFunctor (j₁.{u} 2 0)) i :=
  Diagram.lift_cell _ i

lemma cooperation_endpoint (b : Bool) : endpoint.{u} 2 b ≫ cooperation.{u} =
    composition.{u} 2 0 (by decide) ≫ cutEndpoint.{u} 2 0 b := by
  apply GlobeComplex.functor_ext
  change cooperation.map ((endpoint.{u} 2 b).map (topTable 2)) =
    (cutEndpoint.{u} 2 0 b).map ((composition.{u} 2 0 (by decide)).map (topTable 2))
  rw [endpoint_top, cooperation_cell]
  rw [composition, lift_top]
  unfold compositeCell
  rw [(cutEndpoint.{u} 2 0 b).map_comp _ _ _ _ ((cutEndpoint.{u} 2 0 b).map_composable (top_composable.{u} 2 0))]
  have h₀ : (cutEndpoint.{u} 2 0 b).map ((i₀.{u} 2 0).map (topTable 2)) =
      (j₀.{u} 2 0).map (cell (if b then 20 else 2)) := by
    change ((i₀.{u} 2 0) ≫ cutEndpoint.{u} 2 0 b).map _ = _
    simp only [cutEndpoint, i₀, pushout.inl_desc]
    change (j₀.{u} 2 0).map ((endpoint.{u} 2 b).map (topTable 2)) = _
    rw [endpoint_top]
  have h₁ : (cutEndpoint.{u} 2 0 b).map ((i₁.{u} 2 0).map (topTable 2)) =
      (j₁.{u} 2 0).map (cell (if b then 20 else 2)) := by
    change ((i₁.{u} 2 0) ≫ cutEndpoint.{u} 2 0 b).map _ = _
    simp only [cutEndpoint, i₁, pushout.inr_desc]
    change (j₁.{u} 2 0).map ((endpoint.{u} 2 b).map (topTable 2)) = _
    rw [endpoint_top]
  simp only [h₀, h₁]
  cases b <;> dsimp only [Bool.false_eq_true, ite_false, ite_true, pastedObj, diagramOfFunctor]
  · exact (Q.{u} 2 0).join_eq _ _ _ _
  · exact (Q.{u} 2 0).join_eq _ _ _ _

lemma projection_cell (i : Fin 23) :
    (projection.{u} 2).map (cell.{u} i) =
      truncate (projectionIndex i).1 (projectionIndex i).2 (topTable 2) := by
  apply Table.ext
  funext p b
  rcases p with _ | _ | _ | p
  · apply Subtype.ext
    funext ⟨a⟩
    revert i b a
    decide
  · apply Subtype.ext
    funext ⟨a⟩
    revert i b a
    decide
  · apply Subtype.ext
    funext ⟨a⟩
    revert i b a
    decide
  · exact (chain_zero (show 2 < p+3 by omega) _).trans
      (chain_zero (show 2 < p+3 by omega) _).symm

lemma map_projection_cell {X : OmegaCategory.{v}} (F : OmegaCategory.Functor (G.{u} 2) X)
    (i : Fin 23) :
    F.map ((projection.{u} 2).map (cell i)) =
      X.face (projectionIndex i).1 (projectionIndex i).2 (F.map (topTable 2)) := by
  rw [projection_cell, ← face_nu]
  erw [F.map_face]

lemma cutProjection_left_cell (i : Fin 23) :
    (cutProjection.{u} 2 0).map ((j₀.{u} 2 0).map (cell i)) =
      (P.{u} 2 0).face (projectionIndex i).1 (projectionIndex i).2
        ((i₀.{u} 2 0).map (topTable 2)) := by
  change ((j₀.{u} 2 0) ≫ cutProjection.{u} 2 0).map _ = _
  simp only [cutProjection, j₀, pushout.inl_desc]
  exact map_projection_cell (i₀.{u} 2 0) i

lemma cutProjection_right_cell (i : Fin 23) :
    (cutProjection.{u} 2 0).map ((j₁.{u} 2 0).map (cell i)) =
      (P.{u} 2 0).face (projectionIndex i).1 (projectionIndex i).2
        ((i₁.{u} 2 0).map (topTable 2)) := by
  change ((j₁.{u} 2 0) ≫ cutProjection.{u} 2 0).map _ = _
  simp only [cutProjection, j₁, pushout.inr_desc]
  exact map_projection_cell (i₁.{u} 2 0) i

lemma cooperation_projection : cooperation.{u} ≫ cutProjection.{u} 2 0 =
    projection.{u} 2 ≫ composition.{u} 2 0 (by decide) := by
  let C := P.{u} 2 0
  let a : C.Cell := (i₀.{u} 2 0).map (topTable 2)
  let b : C.Cell := (i₁.{u} 2 0).map (topTable 2)
  have ha : C.source 2 a = a := by
    erw [← (i₀.{u} 2 0).map_source]
    change (i₀.{u} 2 0).map (truncate 2 false (topTable 2)) = _
    rw [topTable_bounded]
  have hb : C.source 2 b = b := by
    erw [← (i₁.{u} 2 0).map_source]
    change (i₁.{u} 2 0).map (truncate 2 false (topTable 2)) = _
    rw [topTable_bounded]
  have hab : C.target 0 a = C.source 0 b := top_composable 2 0
  let L := diagramOfFunctor (j₀.{u} 2 0)
  let R := diagramOfFunctor (j₁.{u} 2 0)
  let F := cutProjection.{u} 2 0
  have hL (i : Fin 23) : (L.map F).obj i = C.face (projectionIndex i).1 (projectionIndex i).2 a :=
    cutProjection_left_cell i
  have hR (i : Fin 23) : (R.map F).obj i = C.face (projectionIndex i).1 (projectionIndex i).2 b :=
    cutProjection_right_cell i
  apply functor_ext_generators
  intro i
  change F.map (cooperation.map (cell (generators i))) =
    (composition.{u} 2 0 (by decide)).map ((projection.{u} 2).map (cell (generators i)))
  rw [cooperation_cell, map_pastedObj L R pushout_glue F, map_projection_cell]
  rw [composition, lift_top]
  change pastedObj (L.map F) (R.map F) (generators i) =
    C.face (projectionIndex (generators i)).1 (projectionIndex (generators i)).2 (C.comp 0 a b hab)
  rw [← C.join_eq]
  exact pastedObj_projection (L.map F) (R.map F) a b ha hb hab hL hR i

theorem firstMixedCooperation : FirstMixedCooperation.{u} :=
  ⟨cooperation, cooperation_endpoint, cooperation_projection⟩
end Thomason.GrayTwo

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open OmegaCategory

namespace Diagram

@[ext] lemma ext {X : OmegaCategory.{v}} {D E : Diagram X}
    (h : ∀ i, D.obj i = E.obj i) : D = E := by
  cases D
  cases E
  congr
  exact funext h

lemma ext_generators {X : OmegaCategory.{v}} {D E : Diagram X}
    (h : ∀ i, D.obj (generators i) = E.obj (generators i)) : D = E := by
  have hh : (D.lift : OmegaCategory.Functor K.{0}.nu X) = E.lift := by
    apply functor_ext_generators
    simpa only [lift_cell] using h
  apply ext
  intro i
  have hh' := congrArg (fun F : OmegaCategory.Functor K.{0}.nu X => F.map (cell i)) hh
  simpa only [lift_cell] using hh'

lemma map_paste {X : OmegaCategory.{v}} {Y : OmegaCategory.{w}}
    (L R : Diagram X) (h : L.obj 17 = R.obj 4) (F : OmegaCategory.Functor X Y) :
    (paste L R h).map F = paste (L.map F) (R.map F) (congrArg F.map h) := by
  apply ext
  intro i
  exact map_pastedObj L R h F i

end Diagram

section Associativity
variable {X : OmegaCategory.{v}} (L R S : Diagram X)
    (hLR : L.obj 17 = R.obj 4) (hRS : R.obj 17 = S.obj 4)

attribute [local simp] Diagram.source_obj Diagram.target_obj
  Diagram.obj5 Diagram.obj7 Diagram.obj8 Diagram.obj9 Diagram.obj11
  Diagram.obj13 Diagram.obj14 Diagram.obj15
  OmegaCategory.join_source_le OmegaCategory.join_source_gt
  OmegaCategory.join_target_le OmegaCategory.join_target_gt
  OmegaCategory.join_assoc

include hRS in
lemma paste_glue_left : (paste L R hLR).obj 17 = S.obj 4 := hRS
include hLR in
lemma paste_glue_right : L.obj 17 = (paste R S hRS).obj 4 := hLR

lemma paste_assoc : paste (paste L R hLR) S (paste_glue_left L R S hLR hRS) =
    paste L (paste R S hRS) (paste_glue_right L R S hLR hRS) := by
  have hsLR := glue_source L R hLR
  have htLR := glue_target L R hLR
  have hsRS := glue_source R S hRS
  have htRS := glue_target R S hRS
  apply Diagram.ext_generators
  intro i
  fin_cases i
  · change pastedObj (paste L R hLR) S 2 = pastedObj L (paste R S hRS) 2
    simp [pastedObj, join_assoc, faceIndex, hsLR, hsRS]
  · rfl
  · change pastedObj (paste L R hLR) S 6 = pastedObj L (paste R S hRS) 6
    simp [pastedObj, join_whisker_right, join_whisker_left, join_assoc,
      faceIndex, hLR, hRS, hsLR, htLR, hsRS, htRS]
    apply X.join_assoc
    all_goals simp [faceIndex, hLR, hRS, hsLR, htLR, hsRS, htRS]
  · change pastedObj (paste L R hLR) S 10 = pastedObj L (paste R S hRS) 10
    simp [pastedObj, join_whisker_right, join_whisker_left, join_assoc,
      faceIndex, hLR, hRS, hsLR, htLR, hsRS, htRS]
    apply X.join_assoc
    all_goals simp [faceIndex, hLR, hRS, hsLR, htLR, hsRS, htRS]
  · change pastedObj (paste L R hLR) S 12 = pastedObj L (paste R S hRS) 12
    simp [pastedObj, join_whisker_right, join_whisker_left, join_assoc,
      faceIndex, hLR, hRS, hsLR, htLR, hsRS, htRS]
    apply X.join_assoc
    all_goals simp [faceIndex, hLR, hRS, hsLR, htLR, hsRS, htRS]
  · rfl
  · change pastedObj (paste L R hLR) S 20 = pastedObj L (paste R S hRS) 20
    simp [pastedObj, join_assoc, faceIndex, htLR, htRS]

end Associativity
end Thomason.GrayTwo

end

noncomputable section
universe u v w z


namespace Thomason.GrayTwo
open OmegaCategory

section Constant
variable {X : OmegaCategory.{v}} (a : X.Cell) (ha : X.source 1 a = a)

def constantObj (i : Fin 23) : X.Cell :=
  match i.val with
  | 0 | 1 | 2 | 3 | 16 => X.source 0 a
  | 18 | 19 | 20 | 21 | 22 => X.target 0 a
  | _ => a

include ha in
lemma constantObj_bounded (i : Fin 23) : X.source 1 (constantObj a i) = constantObj a i := by
  fin_cases i <;> simp [constantObj, X.source_source, X.source_target, ha]

include ha in
lemma constantObj_faces (k : ℕ) (b : Bool) (i : Fin 23) :
    X.face k b (constantObj a i) = constantObj a (faceIndex k b i) := by
  have ht : X.target 1 a = a := X.target_eq_self_of_source_eq_self ha
  have hs₂ : X.source 2 a = a := X.source_fixed_upwards (by decide : 1 ≤ 2) ha
  have ht₂ : X.target 2 a = a := X.target_eq_self_of_source_eq_self hs₂
  rcases k with _ | _ | _ | k
  · fin_cases i <;> cases b <;> simp [constantObj, faceIndex, face,
      X.source_source, X.source_target, X.target_source, X.target_target]
  · fin_cases i <;> cases b <;> simp [constantObj, faceIndex, face, ha, ht,
      X.source_source, X.source_target, X.target_source, X.target_target]
  · fin_cases i <;> cases b <;> simp [constantObj, faceIndex, face, hs₂, ht₂,
      X.source_source, X.source_target, X.target_source, X.target_target]
  · exact X.face_of_fixed (constantObj_bounded a ha i) (by omega) b

def constant : Diagram X where
  obj := constantObj a
  faces := constantObj_faces a ha
  composites e := by
    rw [← X.join_eq]
    have ht : X.target 1 a = a := X.target_eq_self_of_source_eq_self ha
    fin_cases e <;> simp [constantObj, composite, join_left_unit, join_right_unit,
      X.source_source, X.source_target, X.target_source, ha, ht]

@[simp] lemma constant_obj (i : Fin 23) : (constant a ha).obj i = constantObj a i := rfl

end Constant

section Unit
variable {X : OmegaCategory.{v}} (D : Diagram X)

lemma obj4_bounded : X.source 1 (D.obj 4) = D.obj 4 := D.source_obj 1 4
lemma obj17_bounded : X.source 1 (D.obj 17) = D.obj 17 := D.source_obj 1 17

lemma constant_left_glue : (constant (D.obj 4) (obj4_bounded D)).obj 17 = D.obj 4 := rfl
lemma constant_right_glue : D.obj 17 = (constant (D.obj 17) (obj17_bounded D)).obj 4 := rfl

attribute [local simp] Diagram.source_obj Diagram.target_obj
  Diagram.obj5 Diagram.obj7 Diagram.obj8 Diagram.obj9 Diagram.obj11
  Diagram.obj13 Diagram.obj14 Diagram.obj15
  OmegaCategory.join_source_le OmegaCategory.join_source_gt
  OmegaCategory.join_target_le OmegaCategory.join_target_gt
  OmegaCategory.join_left_unit OmegaCategory.join_right_unit

lemma paste_left_unit : paste (constant (D.obj 4) (obj4_bounded D)) D
    (constant_left_glue D) = D := by
  apply Diagram.ext_generators
  intro i
  fin_cases i <;> simp [generators, pastedObj, constantObj, faceIndex]

lemma paste_right_unit : paste D (constant (D.obj 17) (obj17_bounded D))
    (constant_right_glue D) = D := by
  apply Diagram.ext_generators
  intro i
  fin_cases i <;> simp [generators, pastedObj, constantObj, faceIndex]

end Unit
end Thomason.GrayTwo

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

def shiftDown (n p : ℕ) : Chain.{u} (n+1) (p+1) ≃ₗ[ℤ] Chain.{u} n p where
  toFun x := ⟨x.val, by
    intro b hb
    apply x.property b
    rcases hb with h | ⟨h, hb⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hb⟩⟩
  invFun x := ⟨x.val, by
    intro b hb
    apply x.property b
    rcases hb with h | ⟨h, hb⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hb⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma shiftDown_coordinate (n p : ℕ) (x : Chain.{u} (n+1) (p+1))
    (i : ULift.{u} Bool) : (shiftDown n p x).val i = x.val i := rfl

@[simp] lemma shiftUp_coordinate (n p : ℕ) (x : Chain.{u} n p) (i : ULift.{u} Bool) :
    ((shiftDown n p).symm x).val i = x.val i := rfl

@[simp] lemma mass_shiftDown (n p : ℕ) (x : Chain.{u} (n+1) (p+1)) :
    mass n p (shiftDown n p x) = mass (n+1) (p+1) x := rfl

@[simp] lemma mass_shiftUp (n p : ℕ) (x : Chain.{u} n p) :
    mass (n+1) (p+1) ((shiftDown n p).symm x) = mass n p x := rfl

@[simp] lemma positive_shiftDown (n p : ℕ) (x : Chain.{u} (n+1) (p+1)) :
    shiftDown n p x ∈ (complex n).positive p ↔ x ∈ (complex (n+1)).positive (p+1) := Iff.rfl

@[simp] lemma positive_shiftUp (n p : ℕ) (x : Chain.{u} n p) :
    (shiftDown n p).symm x ∈ (complex (n+1)).positive (p+1) ↔
      x ∈ (complex n).positive p := Iff.rfl

lemma shiftDown_d (n p : ℕ) (x : Chain.{u} (n+1) (p+2)) :
    shiftDown n p ((complex (n+1)).d (p+1) x) =
      (complex n).d p (shiftDown n (p+1) x) := by
  apply Subtype.ext
  funext ⟨i⟩
  change (((complex (n+1)).d (p+1) x).val ⟨i⟩) = _
  erw [complex_d_coordinate, complex_d_coordinate, mass_shiftDown]

lemma shiftUp_d (n p : ℕ) (x : Chain.{u} n (p+1)) :
    (complex (n+1)).d (p+1) ((shiftDown n (p+1)).symm x) =
      (shiftDown n p).symm ((complex n).d p x) := by
  apply (shiftDown n p).injective
  erw [shiftDown_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def vertexWeights (n : ℕ) (a b : ℤ) : Chain.{u} (n+1) 0 :=
  ⟨fun i => if i.down then b else a, by intro i hi; rcases hi with h | ⟨h, _⟩ <;> omega⟩

@[simp] lemma vertexWeights_coordinate (n : ℕ) (a b : ℤ) (i : Bool) :
    (vertexWeights.{u} n a b).val ⟨i⟩ = if i then b else a := rfl

@[simp] lemma vertexWeights_zero (n : ℕ) : vertexWeights.{u} n 0 0 = 0 := by
  apply Subtype.ext
  funext ⟨i⟩
  cases i <;> rfl

lemma vertexWeights_positive {n : ℕ} {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    vertexWeights.{u} n a b ∈ (complex (n+1)).positive 0 := by
  intro i
  cases i <;> assumption

lemma d_shiftUp_zero (n : ℕ) (x : Chain.{u} n 0) :
    (complex (n+1)).d 0 ((shiftDown n 0).symm x) =
      vertexWeights n (-mass n 0 x) (mass n 0 x) := by
  apply Subtype.ext
  funext ⟨i⟩
  erw [complex_d_coordinate, mass_shiftUp, vertexWeights_coordinate]

lemma vertexWeights_add (n : ℕ) (a b c d : ℤ) :
    vertexWeights.{u} n (a+c) (b+d) = vertexWeights n a b + vertexWeights n c d := by
  apply Subtype.ext
  funext ⟨i⟩
  cases i <;> rfl

lemma mass_d (n p : ℕ) (x : Chain.{u} n (p+1)) :
    mass n p ((complex n).d p x) = 0 := by
  change mass n p (mass n (p+1) x • delta n p) = 0
  rw [map_zsmul, mass_delta, smul_zero]

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

abbrev K (n : ℕ) : DirectedComplex.{u} := (complex n).cylinder

def diagonalRow (n : ℕ) (b : Bool) : (K.{u} (n+1)).Chain 0 :=
  if b then (0, basis (n+1) 0 true (Or.inl (by omega)))
  else (basis (n+1) 0 false (Or.inl (by omega)), 0)

def IsDiagonal {n : ℕ} (t : Table (K.{u} (n+1))) : Prop :=
  ∀ b, t.row 0 b = diagonalRow n b

def downRow (n : ℕ) : (p : ℕ) → (K.{u} (n+1)).Chain (p+1) →+ (K.{u} n).Chain p
  | 0 =>
    { toFun x := (shiftDown n 0 x.2.1, shiftDown n 0 x.1)
      map_zero' := rfl
      map_add' _ _ := rfl }
  | p+1 =>
    { toFun x := (shiftDown n (p+1) x.2.1, shiftDown n (p+1) x.1,
      shiftDown n p x.2.2)
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma downRow_d (n p : ℕ) (x : (K.{u} (n+1)).Chain (p+2)) :
    downRow n p ((K (n+1)).d (p+1) x) = (K n).d p (downRow n (p+1) x) := by
  cases p with
  | zero =>
    apply Prod.ext
    · change shiftDown n 0 ((complex (n+1)).d 1 x.2.1 + (-1 : ℤ) • x.2.2) =
        differential n 0 (shiftDown n 1 x.2.1) - shiftDown n 0 x.2.2
      erw [map_add, map_zsmul (shiftDown n 0) (-1) x.2.2, shiftDown_d]
      simp [complex, sub_eq_add_neg]
      rfl
    · change shiftDown n 0 ((complex (n+1)).d 1 x.1 - (-1 : ℤ) • x.2.2) =
        differential n 0 (shiftDown n 1 x.1) + shiftDown n 0 x.2.2
      erw [map_sub, map_zsmul (shiftDown n 0) (-1) x.2.2, shiftDown_d]
      simp [complex]
      rfl
  | succ p =>
    apply Prod.ext
    · change shiftDown n (p+1) ((complex (n+1)).d (p+2) x.2.1 +
        (-1 : ℤ)^(p+2) • x.2.2) =
          differential n (p+1) (shiftDown n (p+2) x.2.1) -
          (-1 : ℤ)^(p+1) • shiftDown n (p+1) x.2.2
      erw [map_add, map_zsmul (shiftDown n (p+1)) ((-1)^(p+2)) x.2.2, shiftDown_d]
      simp [complex, pow_succ, sub_eq_add_neg]
      rfl
    · apply Prod.ext
      · change shiftDown n (p+1) ((complex (n+1)).d (p+2) x.1 -
          (-1 : ℤ)^(p+2) • x.2.2) =
            differential n (p+1) (shiftDown n (p+2) x.1) +
            (-1 : ℤ)^(p+1) • shiftDown n (p+1) x.2.2
        erw [map_sub, map_zsmul (shiftDown n (p+1)) ((-1)^(p+2)) x.2.2, shiftDown_d]
        simp [complex, pow_succ, sub_eq_add_neg]
        rfl
      · exact shiftDown_d n p x.2.2

lemma downRow_positive (n p : ℕ) (x : (K.{u} (n+1)).Chain (p+1))
    (hx : x ∈ (K (n+1)).positive (p+1)) :
    downRow n p x ∈ (K n).positive p := by
  cases p with
  | zero => exact ⟨hx.2.1, hx.1⟩
  | succ p => exact ⟨hx.2.1, hx.1, hx.2.2⟩

lemma diagonal_row_one {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (b : Bool) :
    mass (n+1) 1 (t.row 1 b).1 + mass (n+1) 1 (t.row 1 b).2.1 = 1 ∧
      (t.row 1 b).2.2 = vertexWeights n (mass (n+1) 1 (t.row 1 b).2.1)
        (mass (n+1) 1 (t.row 1 b).1) := by
  have h := t.boundary 0 b
  rw [ht true, ht false] at h
  have h₀ := congrArg (fun x : (K (n+1)).Chain 0 => x.1.val ⟨false⟩) h
  have h₁ := congrArg (fun x : (K (n+1)).Chain 0 => x.1.val ⟨true⟩) h
  have h₂ := congrArg (fun x : (K (n+1)).Chain 0 => x.2.val ⟨false⟩) h
  change (((complex (n+1)).d 0 (t.row 1 b).1).val ⟨false⟩) -
    (t.row 1 b).2.2.val ⟨false⟩ = -1 at h₀
  change (((complex (n+1)).d 0 (t.row 1 b).1).val ⟨true⟩) -
    (t.row 1 b).2.2.val ⟨true⟩ = 0 at h₁
  change (((complex (n+1)).d 0 (t.row 1 b).2.1).val ⟨false⟩) +
    (t.row 1 b).2.2.val ⟨false⟩ = 0 at h₂
  erw [complex_d_coordinate] at h₀ h₁ h₂
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁ h₂
  dsimp [mass] at h₀ h₁ h₂ ⊢
  refine ⟨by omega, ?_⟩
  apply Subtype.ext
  funext ⟨i⟩
  change (t.row 1 b).2.2.val ⟨i⟩ = if i then _ else _
  cases i <;> dsimp [mass] <;> omega

def down {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) : Table (K.{u} n) where
  row p b := downRow n p (t.row (p+1) b)
  positive p b := downRow_positive n p _ (t.positive (p+1) b)
  boundary p b := by
    rw [← downRow_d, t.boundary, map_sub]
  augmentation b := by
    change mass (n+1) 1 (t.row 1 b).2.1 + mass (n+1) 1 (t.row 1 b).1 = 1
    rw [add_comm]
    exact (diagonal_row_one t ht b).1
  bounded := by
    obtain ⟨k, hk⟩ := t.bounded
    refine ⟨k, fun p hp b => ?_⟩
    rw [hk (p+1) (by omega) b, map_zero]

@[simp] lemma down_row {n p : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (b : Bool) :
    (down t ht).row p b = downRow n p (t.row (p+1) b) := rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def upRow (n : ℕ) : (p : ℕ) → (K.{u} n).Chain p →+ (K.{u} (n+1)).Chain (p+1)
  | 0 =>
    { toFun x := ((shiftDown n 0).symm x.2, (shiftDown n 0).symm x.1,
        vertexWeights n (mass n 0 x.1) (mass n 0 x.2))
      map_zero' := by
        apply Prod.ext
        · rfl
        · exact Prod.ext rfl (vertexWeights_zero n)
      map_add' first second := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · change vertexWeights n (mass n 0 (first.1 + second.1))
              (mass n 0 (first.2 + second.2)) = _
            erw [map_add, map_add]
            exact vertexWeights_add n _ _ _ _ }
  | p+1 =>
    { toFun x := ((shiftDown n (p+1)).symm x.2.1, (shiftDown n (p+1)).symm x.1,
        (shiftDown n p).symm x.2.2)
      map_zero' := rfl
      map_add' _ _ := rfl }

private lemma upRow_d_zero (n : ℕ) (x : (K.{u} n).Chain 1) :
    upRow n 0 ((K n).d 0 x) = (K (n+1)).d 1 (upRow n 1 x) := by
  apply Prod.ext
  · change (shiftDown n 0).symm ((complex n).d 0 x.2.1 + x.2.2) =
      differential (n+1) 1 ((shiftDown n 1).symm x.2.1) -
        (-1 : ℤ) • (shiftDown n 0).symm x.2.2
    erw [map_add, shiftUp_d]
    simp
  · apply Prod.ext
    · change (shiftDown n 0).symm ((complex n).d 0 x.1 - x.2.2) =
        differential (n+1) 1 ((shiftDown n 1).symm x.1) +
          (-1 : ℤ) • (shiftDown n 0).symm x.2.2
      erw [map_sub, shiftUp_d]
      simp [sub_eq_add_neg]
    · change vertexWeights n (mass n 0 ((complex n).d 0 x.1 - x.2.2))
        (mass n 0 ((complex n).d 0 x.2.1 + x.2.2)) =
          (complex (n+1)).d 0 ((shiftDown n 0).symm x.2.2)
      erw [map_sub, map_add, mass_d, mass_d, d_shiftUp_zero]
      simp only [zero_sub, zero_add]

private lemma upRow_d_succ (n p : ℕ) (x : (K.{u} n).Chain (p+2)) :
    upRow n (p+1) ((K n).d (p+1) x) =
      (K (n+1)).d (p+2) (upRow n (p+2) x) := by
  apply Prod.ext
  · change (shiftDown n (p+1)).symm ((complex n).d (p+1) x.2.1 +
      (-1 : ℤ)^(p+1) • x.2.2) =
        differential (n+1) (p+2) ((shiftDown n (p+2)).symm x.2.1) -
          (-1 : ℤ)^(p+2) • (shiftDown n (p+1)).symm x.2.2
    erw [map_add, map_zsmul (shiftDown n (p+1)).symm ((-1)^(p+1)) x.2.2, shiftUp_d]
    simp [pow_succ, sub_eq_add_neg]
    rfl
  · apply Prod.ext
    · change (shiftDown n (p+1)).symm ((complex n).d (p+1) x.1 -
        (-1 : ℤ)^(p+1) • x.2.2) =
          differential (n+1) (p+2) ((shiftDown n (p+2)).symm x.1) +
            (-1 : ℤ)^(p+2) • (shiftDown n (p+1)).symm x.2.2
      erw [map_sub, map_zsmul (shiftDown n (p+1)).symm ((-1)^(p+1)) x.2.2, shiftUp_d]
      simp [pow_succ, sub_eq_add_neg]
      rfl
    · change (shiftDown n p).symm ((complex n).d p x.2.2) =
        (complex (n+1)).d (p+1) ((shiftDown n (p+1)).symm x.2.2)
      exact (shiftUp_d n p x.2.2).symm

lemma upRow_d (n p : ℕ) (x : (K.{u} n).Chain (p+1)) :
    upRow n p ((K n).d p x) = (K (n+1)).d (p+1) (upRow n (p+1) x) := by
  cases p with
  | zero => exact upRow_d_zero n x
  | succ p => exact upRow_d_succ n p x

lemma downRow_upRow (n p : ℕ) (x : (K.{u} n).Chain p) : downRow n p (upRow n p x) = x := by
  cases p <;> rfl

lemma upRow_downRow_succ (n p : ℕ) (x : (K.{u} (n+1)).Chain (p+2)) :
    upRow n (p+1) (downRow n (p+1) x) = x := by
  rfl

lemma upRow_downRow_zero {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (b : Bool) :
    upRow n 0 (downRow n 0 (t.row 1 b)) = t.row 1 b := by
  exact Prod.ext rfl (Prod.ext rfl (diagonal_row_one t ht b).2.symm)

lemma upRow_positive (n p : ℕ) (x : (K.{u} n).Chain p) (hx : x ∈ (K n).positive p) :
    upRow n p x ∈ (K (n+1)).positive (p+1) := by
  cases p with
  | zero => exact ⟨hx.2, hx.1, vertexWeights_positive (mass_nonneg hx.1) (mass_nonneg hx.2)⟩
  | succ p => exact ⟨hx.2.1, hx.1, hx.2.2⟩

lemma upRow_zero_d (n : ℕ) (x : (K.{u} n).Chain 0) (hx : (K n).augmentation x = 1) :
    (K (n+1)).d 0 (upRow n 0 x) = diagonalRow n true - diagonalRow n false := by
  change mass n 0 x.1 + mass n 0 x.2 = 1 at hx
  apply Prod.ext
  · apply Subtype.ext
    funext ⟨i⟩
    change (((complex (n+1)).d 0 ((shiftDown n 0).symm x.2)).val ⟨i⟩) -
      (vertexWeights.{u} n (mass n 0 x.1) (mass n 0 x.2)).val ⟨i⟩ =
      0 - (basis.{u} (n+1) 0 false (Or.inl (by omega))).val ⟨i⟩
    erw [complex_d_coordinate, mass_shiftUp, vertexWeights_coordinate, basis_coordinate]
    cases i <;> dsimp <;> omega
  · apply Subtype.ext
    funext ⟨i⟩
    change (((complex (n+1)).d 0 ((shiftDown n 0).symm x.1)).val ⟨i⟩) +
      (vertexWeights.{u} n (mass n 0 x.1) (mass n 0 x.2)).val ⟨i⟩ =
      (basis.{u} (n+1) 0 true (Or.inl (by omega))).val ⟨i⟩ - 0
    erw [complex_d_coordinate, mass_shiftUp, vertexWeights_coordinate, basis_coordinate]
    cases i <;> dsimp <;> omega

def up {n : ℕ} (t : Table (K.{u} n)) : Table (K.{u} (n+1)) where
  row
    | 0, b => diagonalRow n b
    | p+1, b => upRow n p (t.row p b)
  positive p b := by
    cases p with
    | zero =>
      cases b
      · exact ⟨basis_positive _ _ _ (Or.inl (by omega)), (complex (n+1)).positive 0 |>.zero_mem⟩
      · exact ⟨(complex (n+1)).positive 0 |>.zero_mem, basis_positive _ _ _ (Or.inl (by omega))⟩
    | succ p => exact upRow_positive n p _ (t.positive p b)
  boundary p b := by
    cases p with
    | zero => exact upRow_zero_d n (t.row 0 b) (t.augmentation b)
    | succ p => rw [← upRow_d, t.boundary, map_sub]
  augmentation b := by
    change mass (n+1) 0 (diagonalRow n b).1 + mass (n+1) 0 (diagonalRow n b).2 = 1
    cases b <;> simp [diagonalRow, mass, basis] <;> rfl
  bounded := by
    obtain ⟨k, hk⟩ := t.bounded
    refine ⟨k+1, ?_⟩
    rintro (_ | p) hp b
    · omega
    · change upRow n p (t.row p b) = 0
      rw [hk p (by omega) b, map_zero]

@[simp] lemma up_zero {n : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    (up t).row 0 b = diagonalRow n b := rfl

@[simp] lemma up_succ {n p : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    (up t).row (p+1) b = upRow n p (t.row p b) := rfl

lemma up_diagonal {n : ℕ} (t : Table (K.{u} n)) : IsDiagonal (up t) := fun _ => rfl

lemma down_up {n : ℕ} (t : Table (K.{u} n)) : down (up t) (up_diagonal t) = t := by
  ext p b
  exact downRow_upRow n p (t.row p b)

lemma up_down {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) : up (down t ht) = t := by
  ext p b
  cases p with
  | zero => exact (ht b).symm
  | succ p =>
    change upRow n p (downRow n p (t.row (p+1) b)) = t.row (p+1) b
    cases p with
    | zero => exact upRow_downRow_zero t ht b
    | succ p => exact upRow_downRow_succ n p (t.row (p+2) b)

def diagonalEquiv (n : ℕ) : {t : Table (K.{u} (n+1)) // IsDiagonal t} ≃ Table (K.{u} n) where
  toFun t := down t.val t.property
  invFun t := ⟨up t, up_diagonal t⟩
  left_inv t := Subtype.ext (up_down t.val t.property)
  right_inv := down_up

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def homCategory (C : OmegaCategory.{u}) (a b : C.Cell) : OmegaCategory.{u} where
  Cell := {x : C.Cell // C.source 0 x = a ∧ C.target 0 x = b}
  source k x := ⟨C.source (k+1) x.val, by
    simpa only [C.source_source, C.target_source, Nat.zero_min, Nat.zero_lt_succ,
      ite_true] using x.property⟩
  target k x := ⟨C.target (k+1) x.val, by
    simpa only [C.source_target, C.target_target, Nat.zero_min, Nat.zero_lt_succ,
      ite_true] using x.property⟩
  source_source i j x := Subtype.ext (by
    change C.source (i+1) (C.source (j+1) x.val) = C.source (min i j + 1) x.val
    rw [C.source_source, Nat.add_min_add_right])
  target_target i j x := Subtype.ext (by
    change C.target (i+1) (C.target (j+1) x.val) = C.target (min i j + 1) x.val
    rw [C.target_target, Nat.add_min_add_right])
  source_target i j x := by
    apply Subtype.ext
    by_cases h : i < j
    · simp only [h, ite_true]
      exact (C.source_target (i+1) (j+1) x.val).trans (ite_eq_left (by omega))
    · simp only [h, ite_false]
      exact (C.source_target (i+1) (j+1) x.val).trans (ite_eq_right (by omega))
  target_source i j x := by
    apply Subtype.ext
    by_cases h : i < j
    · simp only [h, ite_true]
      exact (C.target_source (i+1) (j+1) x.val).trans (ite_eq_left (by omega))
    · simp only [h, ite_false]
      exact (C.target_source (i+1) (j+1) x.val).trans (ite_eq_right (by omega))
  comp k x y h := ⟨C.comp (k+1) x.val y.val (congrArg Subtype.val h), by
    constructor
    · rw [C.source_comp_le 0 (k+1) (by omega)]
      exact x.property.1
    · rw [C.target_comp_le 0 (k+1) (by omega)]
      exact y.property.2⟩
  source_comp_le i k h x y e :=
    Subtype.ext (C.source_comp_le (i+1) (k+1) (by omega) x.val y.val (congrArg Subtype.val e))
  target_comp_le i k h x y e :=
    Subtype.ext (C.target_comp_le (i+1) (k+1) (by omega) x.val y.val (congrArg Subtype.val e))
  source_comp_gt i k h x y e es :=
    Subtype.ext (C.source_comp_gt (i+1) (k+1) (by omega) x.val y.val
      (congrArg Subtype.val e) (congrArg Subtype.val es))
  target_comp_gt i k h x y e et :=
    Subtype.ext (C.target_comp_gt (i+1) (k+1) (by omega) x.val y.val
      (congrArg Subtype.val e) (congrArg Subtype.val et))
  unit_left k x h := Subtype.ext (C.unit_left (k+1) x.val (congrArg Subtype.val h))
  unit_right k x h := Subtype.ext (C.unit_right (k+1) x.val (congrArg Subtype.val h))
  assoc k x y z hxy hyz hxy_z hx_yz :=
    Subtype.ext (C.assoc (k+1) x.val y.val z.val (congrArg Subtype.val hxy)
      (congrArg Subtype.val hyz) (congrArg Subtype.val hxy_z) (congrArg Subtype.val hx_yz))
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd :=
    Subtype.ext (C.interchange (k+1) (l+1) (by omega) a.val b.val c.val d.val
      (congrArg Subtype.val hab) (congrArg Subtype.val hcd) (congrArg Subtype.val hac)
      (congrArg Subtype.val hbd) (congrArg Subtype.val hab_cd) (congrArg Subtype.val hac_bd))
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x.val
    exact ⟨k, Subtype.ext (C.source_fixed_upwards (by omega : k ≤ k+1) hk)⟩

namespace Functor
variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}

def homMap (F : Functor C D) (a b : C.Cell) :
    Functor (C.homCategory a b) (D.homCategory (F.map a) (F.map b)) where
  map x := ⟨F.map x.val, by
    rw [← F.map_source, ← F.map_target, x.property.1, x.property.2]
    exact ⟨rfl, rfl⟩⟩
  map_source k x := Subtype.ext (F.map_source (k+1) x.val)
  map_target k x := Subtype.ext (F.map_target (k+1) x.val)
  map_comp k x y h h' :=
    Subtype.ext (F.map_comp (k+1) x.val y.val (congrArg Subtype.val h) (congrArg Subtype.val h'))

end Functor

lemma homCategory_truncated (C : OmegaCategory.{u}) (n : ℕ) (h : C.IsTruncated (n+1))
    (a b : C.Cell) : (C.homCategory a b).IsTruncated n :=
  fun x => Subtype.ext (h x.val)

end Thomason.OmegaCategory

end

end OAI
