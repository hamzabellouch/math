import Mathlib
import OAI.CategoryTheory.Thomason.BoundedCylinders

namespace OAI

/-! Two Cell Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X : OmegaCategory.{u}}

lemma crossingEdge_source_one (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).source 1 (crossingEdge l c r) =
      crossingEdge (X.source 1 l) c (X.source 1 r) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
      (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl),
    endpoint_source, endpoint_source, verticalObject_bounded]

lemma crossingEdge_target_one (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).target 1 (crossingEdge l c r) =
      crossingEdge (X.target 1 l) c (X.target 1 r) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
      (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl),
    endpoint_target, endpoint_target,
    (tensorFunctor.obj X).target_eq_self_of_source_eq_self (verticalObject_bounded c)]

lemma crossingEdge_bounded_two (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val)
    (hdl : X.source 2 l = l) (hdr : X.source 2 r = r) :
    (tensorFunctor.obj X).source 2 (crossingEdge l c r) = crossingEdge l c r := by
  unfold crossingEdge
  apply composite_bounded _ (by omega : 0 < 2) _ _
  · exact composite_bounded _ (by omega : 0 < 2) _ _
      ((endpoint_source false 2 l).trans (congrArg ((tensorEndpoint false).app X).map hdl))
      ((tensorFunctor.obj X).source_fixed_upwards (by omega : 1 ≤ 2) (verticalObject_bounded c))
      (crossingEdge_left_matching l c hl)
  · exact (endpoint_source true 2 r).trans (congrArg ((tensorEndpoint true).app X).map hdr)
  · exact crossingEdge_right_matching l c r hl hr

structure CrossingSquare (X : OmegaCategory.{u}) where
  left : X.Cells 1
  cross : X.Cells 1
  right : X.Cells 1
  left₂ : X.Cells 2
  right₂ : X.Cells 2
  lc : X.target 0 left.val = X.source 0 cross.val
  cr : X.target 0 cross.val = X.source 0 right.val
  left_source : X.source 1 left₂.val = X.join 0 left.val cross.val
  right_target : X.target 1 right₂.val = X.join 0 cross.val right.val

namespace CrossingSquare
variable (D : CrossingSquare X)

abbrev entry : X.Objects := ⟨X.source 0 D.cross.val, X.source_source_self 0 D.cross.val⟩
abbrev exit : X.Objects := ⟨X.target 0 D.cross.val, X.source_target_self 0 D.cross.val⟩

lemma left₂_source_zero : X.source 0 D.left₂.val = X.source 0 D.left.val := by
  have h := congrArg (X.source 0) D.left_source
  rw [X.source_source, min_eq_left (by omega : 0 ≤ 1),
    X.join_source_le 0 0 _ _ le_rfl D.lc] at h
  exact h

lemma left₂_target_zero : X.target 0 D.left₂.val = D.exit.val := by
  have h := congrArg (X.target 0) D.left_source
  rw [X.target_source, ite_eq_left (by omega : 0 < 1),
    X.join_target_le 0 0 _ _ le_rfl D.lc] at h
  exact h

lemma right₂_source_zero : X.source 0 D.right₂.val = D.entry.val := by
  have h := congrArg (X.source 0) D.right_target
  rw [X.source_target, ite_eq_left (by omega : 0 < 1),
    X.join_source_le 0 0 _ _ le_rfl D.cr] at h
  exact h

lemma right₂_target_zero : X.target 0 D.right₂.val = X.target 0 D.right.val := by
  have h := congrArg (X.target 0) D.right_target
  rw [X.target_target, min_eq_left (by omega : 0 ≤ 1),
    X.join_target_le 0 0 _ _ le_rfl D.cr] at h
  exact h

def middle : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map D.left.val)
      (verticalCell 1 D.cross)) (((tensorEndpoint true).app X).map D.right.val)

def first : (tensorFunctor.obj X).Cell := crossingEdge D.left.val D.entry D.right₂.val

def last : (tensorFunctor.obj X).Cell := crossingEdge D.left₂.val D.exit D.right.val

lemma vertical_source_zero (a : X.Cells 1) :
    (tensorFunctor.obj X).source 0 (verticalCell 1 a) =
      ((tensorEndpoint false).app X).map (X.source 0 a.val) := by
  have h := congrArg ((tensorFunctor.obj X).source 0) (verticalCell_one_face a false)
  change (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).source 1 (verticalCell 1 a)) = _ at h
  rw [(tensorFunctor.obj X).source_source, min_eq_left (by omega : 0 ≤ 1)] at h
  simp only [Bool.false_eq_true, ite_false] at h
  have hm : (tensorFunctor.obj X).target 0
      (verticalObject ⟨X.source 0 a.val, X.source_source_self 0 a.val⟩) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map a.val) := by
    erw [verticalObject_target, endpoint_source]
  erw [(tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl hm, verticalObject_source] at h
  exact h

lemma vertical_target_zero (a : X.Cells 1) :
    (tensorFunctor.obj X).target 0 (verticalCell 1 a) =
      ((tensorEndpoint true).app X).map (X.target 0 a.val) := by
  have h := congrArg ((tensorFunctor.obj X).target 0) (verticalCell_one_face a true)
  change (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).target 1 (verticalCell 1 a)) = _ at h
  rw [(tensorFunctor.obj X).target_target, min_eq_left (by omega : 0 ≤ 1)] at h
  simp only [ite_true] at h
  have hm : (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map a.val) =
      (tensorFunctor.obj X).source 0
        (verticalObject ⟨X.target 0 a.val, X.source_target_self 0 a.val⟩) := by
    erw [verticalObject_source, endpoint_target]
  erw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl hm, verticalObject_target] at h
  exact h

lemma middle_matching_left :
    (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map D.left.val) =
      (tensorFunctor.obj X).source 0 (verticalCell 1 D.cross) := by
  rw [endpoint_target, vertical_source_zero, D.lc]

lemma middle_matching_right :
    (tensorFunctor.obj X).target 0
      ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map D.left.val)
        (verticalCell 1 D.cross)) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map D.right.val) := by
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl D.middle_matching_left,
    vertical_target_zero, endpoint_source, D.cr]

lemma middle_source : (tensorFunctor.obj X).source 1 D.middle =
    crossingEdge D.left.val D.entry (X.join 0 D.cross.val D.right.val) := by
  unfold middle
  rw [(tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega) D.middle_matching_right,
    (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega) D.middle_matching_left,
    endpoint_source, D.left.property, endpoint_source, D.right.property]
  change (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 _ ((tensorFunctor.obj X).face 1 false (verticalCell 1 D.cross))) _ = _
  rw [verticalCell_one_face]
  simp only [Bool.false_eq_true, ite_false]
  unfold crossingEdge
  have hv : (tensorFunctor.obj X).target 0 (verticalObject D.entry) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map D.cross.val) := by
    rw [verticalObject_target, endpoint_source]
  rw [← (tensorFunctor.obj X).join_assoc 0 _ _ _
      (crossingEdge_left_matching D.left.val D.entry D.lc) hv,
    (tensorFunctor.obj X).join_assoc 0 _ _ _
      (crossingEdge_right_matching D.left.val D.entry D.cross.val D.lc rfl)
      (((tensorEndpoint true).app X).map_composable D.cr),
    ← ((tensorEndpoint true).app X).map_join 0 _ _ D.cr]
  rfl

lemma middle_target : (tensorFunctor.obj X).target 1 D.middle =
    crossingEdge (X.join 0 D.left.val D.cross.val) D.exit D.right.val := by
  unfold middle
  rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega) D.middle_matching_right,
    (tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega) D.middle_matching_left,
    endpoint_target, X.target_eq_self_of_source_eq_self D.left.property,
    endpoint_target, X.target_eq_self_of_source_eq_self D.right.property]
  change (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 _ ((tensorFunctor.obj X).face 1 true (verticalCell 1 D.cross))) _ = _
  rw [verticalCell_one_face]
  simp only [ite_true]
  unfold crossingEdge
  have hv : (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map D.cross.val) =
      (tensorFunctor.obj X).source 0 (verticalObject D.exit) := by
    rw [verticalObject_source, endpoint_target]
  rw [← (tensorFunctor.obj X).join_assoc 0 _ _ _
      (((tensorEndpoint false).app X).map_composable D.lc) hv,
    ← ((tensorEndpoint false).app X).map_join 0 _ _ D.lc]
  rfl

lemma first_source : (tensorFunctor.obj X).source 1 D.first =
    crossingEdge D.left.val D.entry (X.source 1 D.right₂.val) := by
  rw [first, crossingEdge_source_one _ _ _ D.lc D.right₂_source_zero, D.left.property]

lemma first_target : (tensorFunctor.obj X).target 1 D.first =
    crossingEdge D.left.val D.entry (X.join 0 D.cross.val D.right.val) := by
  rw [first, crossingEdge_target_one _ _ _ D.lc D.right₂_source_zero,
    X.target_eq_self_of_source_eq_self D.left.property, D.right_target]

lemma last_source : (tensorFunctor.obj X).source 1 D.last =
    crossingEdge (X.join 0 D.left.val D.cross.val) D.exit D.right.val := by
  rw [last, crossingEdge_source_one _ _ _ D.left₂_target_zero D.cr.symm,
    D.right.property, D.left_source]

lemma last_target : (tensorFunctor.obj X).target 1 D.last =
    crossingEdge (X.target 1 D.left₂.val) D.exit D.right.val := by
  rw [last, crossingEdge_target_one _ _ _ D.left₂_target_zero D.cr.symm,
    X.target_eq_self_of_source_eq_self D.right.property]

lemma first_middle : (tensorFunctor.obj X).target 1 D.first =
    (tensorFunctor.obj X).source 1 D.middle := D.first_target.trans D.middle_source.symm

lemma middle_last : (tensorFunctor.obj X).target 1 D.middle =
    (tensorFunctor.obj X).source 1 D.last := D.middle_target.trans D.last_source.symm

lemma firstMiddle_last : (tensorFunctor.obj X).target 1
    ((tensorFunctor.obj X).join 1 D.first D.middle) = (tensorFunctor.obj X).source 1 D.last := by
  rw [(tensorFunctor.obj X).join_target_le 1 1 _ _ le_rfl D.first_middle]
  exact D.middle_last

def value : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 1 ((tensorFunctor.obj X).join 1 D.first D.middle) D.last

lemma source_one : (tensorFunctor.obj X).source 1 D.value =
    crossingEdge D.left.val D.entry (X.source 1 D.right₂.val) := by
  rw [value, (tensorFunctor.obj X).join_source_le 1 1 _ _ le_rfl D.firstMiddle_last,
    (tensorFunctor.obj X).join_source_le 1 1 _ _ le_rfl D.first_middle, D.first_source]

lemma target_one : (tensorFunctor.obj X).target 1 D.value =
    crossingEdge (X.target 1 D.left₂.val) D.exit D.right.val := by
  rw [value, (tensorFunctor.obj X).join_target_le 1 1 _ _ le_rfl D.firstMiddle_last, D.last_target]

lemma bounded : (tensorFunctor.obj X).source 2 D.value = D.value := by
  apply composite_bounded _ (by omega : 1 < 2) _ _ _ _ D.firstMiddle_last
  · apply composite_bounded _ (by omega : 1 < 2) _ _ _ _ D.first_middle
    · exact crossingEdge_bounded_two _ _ _ D.lc D.right₂_source_zero
        (X.source_fixed_upwards (by omega : 1 ≤ 2) D.left.property) D.right₂.property
    · apply composite_bounded _ (by omega : 0 < 2) _ _ _ _ D.middle_matching_right
      · exact composite_bounded _ (by omega : 0 < 2) _ _
          ((endpoint_source false 2 _).trans (congrArg ((tensorEndpoint false).app X).map
            (X.source_fixed_upwards (by omega : 1 ≤ 2) D.left.property)))
          (verticalCell_bounded 1 D.cross) D.middle_matching_left
      · exact (endpoint_source true 2 _).trans (congrArg ((tensorEndpoint true).app X).map
          (X.source_fixed_upwards (by omega : 1 ≤ 2) D.right.property))
  · exact crossingEdge_bounded_two _ _ _ D.left₂_target_zero D.cr.symm D.left₂.property
      (X.source_fixed_upwards (by omega : 1 ≤ 2) D.right.property)

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
open CylinderTables

variable {M : DirectedComplex.{u}}
lemma table_join_row_above (k p : ℕ) (hkp : k < p) (x y : Table M)
    (h : truncate k true x = truncate k false y) (b : Bool) :
    (M.nu.join k x y).row p b = x.row p b + y.row p b := by
  rw [M.nu.join_eq k x y h]
  change (DirectedComplex.Table.comp k x y h).row p b = _
  simp only [comp_row, show ¬p < k by omega, Ne.symm hkp.ne, ite_false]

namespace CrossingSquare

variable (D : CrossingSquare M.nu)

lemma image_middle : (chainComparison M).map D.middle =
    tableSandwich D.left.val D.cross.val D.right.val := by
  unfold middle tableSandwich
  erw [(chainComparison M).map_join 0 _ _ D.middle_matching_right,
    (chainComparison M).map_join 0 _ _ D.middle_matching_left,
    chainComparison_endpoint_apply false D.left.val,
    chainComparison_endpoint_apply true D.right.val,
    chainComparison_verticalCell 1 D.cross]

lemma image_first : (chainComparison M).map D.first =
    tableSandwich D.left.val D.entry.val D.right₂.val :=
  chainComparison_crossingEdge D.left.val D.entry D.right₂.val D.lc D.right₂_source_zero

lemma image_last : (chainComparison M).map D.last =
    tableSandwich D.left₂.val D.exit.val D.right.val :=
  chainComparison_crossingEdge D.left₂.val D.exit D.right.val D.left₂_target_zero D.cr.symm

lemma image_two (b : Bool) :
    ((chainComparison M).map D.value).row 2 b =
      (D.left₂.val.row 2 b, D.right₂.val.row 2 b, D.cross.val.row 1 b) := by
  have hl : D.left.val.row 0 true = D.cross.val.row 0 false :=
    congrArg (fun t : Table M => t.row 0 false) D.lc
  have hr : D.right.val.row 0 false = D.cross.val.row 0 true :=
    congrArg (fun t : Table M => t.row 0 false) D.cr.symm
  have hleft := row_above_fixed D.left.val D.left.property (by omega : 1 < 2) b
  have hright := row_above_fixed D.right.val D.right.property (by omega : 1 < 2) b
  have hcross := row_above_fixed D.cross.val D.cross.property (by omega : 1 < 2) b
  have hv : verticalRow D.cross.val 2 b = (0, 0, D.cross.val.row 1 b) := by
    cases b <;> simp [verticalRow, hcross]
  unfold value
  rw [(chainComparison M).map_join 1 _ _ D.firstMiddle_last,
    (chainComparison M).map_join 1 _ _ D.first_middle]
  erw [table_join_row_above 1 2 (by omega) _ _ ?_ b,
    table_join_row_above 1 2 (by omega) _ _ ((chainComparison M).map_composable D.first_middle) b]
  rotate_left
  · have hm := (chainComparison M).map_composable D.firstMiddle_last
    rw [(chainComparison M).map_join 1 _ _ D.first_middle] at hm
    exact hm
  rw [show D.first = crossingEdge D.left.val D.entry D.right₂.val from rfl,
    show D.last = crossingEdge D.left₂.val D.exit D.right.val from rfl,
    chainComparison_crossingEdge_row_succ D.left.val D.entry D.right₂.val D.lc D.right₂_source_zero,
    chainComparison_crossingEdge_row_succ D.left₂.val D.exit D.right.val D.left₂_target_zero D.cr.symm,
    D.image_middle,
    tableSandwich_succ _ _ _ hl hr]
  have hs : D.entry.val.row 1 b = 0 :=
    row_above_fixed D.entry.val D.entry.property (by omega : 0 < 1) b
  have ht : D.exit.val.row 1 b = 0 :=
    row_above_fixed D.exit.val D.exit.property (by omega : 0 < 1) b
  rw [hleft, hright, hs, ht, hv]
  change (0, D.right₂.val.row 2 b, 0) +
    ((0 : M.cylinder.Chain 2) + (0, 0, D.cross.val.row 1 b) + 0) +
      (D.left₂.val.row 2 b, 0, 0) = _
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem image_ext (E : CrossingSquare M.nu)
    (h : (chainComparison M).map D.value = (chainComparison M).map E.value) : D = E := by
  have hs := congrArg (M.cylinder.nu.source 1) h
  rw [← (chainComparison M).map_source, ← (chainComparison M).map_source,
    D.source_one, E.source_one] at hs
  have hr (A : CrossingSquare M.nu) :
      truncate 0 false (truncate 1 false A.right₂.val) = A.entry.val := by
    change M.nu.source 0 (M.nu.source 1 A.right₂.val) = _
    rw [M.nu.source_source, min_eq_left (by omega : 0 ≤ 1)]
    exact A.right₂_source_zero
  obtain ⟨hl, hc₀, hR₀⟩ := chainComparison_crossingEdge_injective
    D.left.val E.left.val D.entry E.entry (truncate 1 false D.right₂.val) (truncate 1 false E.right₂.val)
    D.lc (hr D) E.lc (hr E) hs
  have ht := congrArg (M.cylinder.nu.target 1) h
  rw [← (chainComparison M).map_target, ← (chainComparison M).map_target,
    D.target_one, E.target_one] at ht
  have hl' (A : CrossingSquare M.nu) :
      truncate 0 true (truncate 1 true A.left₂.val) = A.exit.val := by
    change M.nu.target 0 (M.nu.target 1 A.left₂.val) = _
    rw [M.nu.target_target, min_eq_left (by omega : 0 ≤ 1)]
    exact A.left₂_target_zero
  obtain ⟨_, _, hr'⟩ := chainComparison_crossingEdge_injective
    (truncate 1 true D.left₂.val) (truncate 1 true E.left₂.val) D.exit E.exit D.right.val E.right.val
    (hl' D) D.cr.symm (hl' E) E.cr.symm ht
  have htop := congrArg (fun t : Table M.cylinder => t.row 2 false) h
  rw [D.image_two, E.image_two] at htop
  have hc : D.cross = E.cross := by
    apply Subtype.ext
    apply ext_source_top D.cross.property E.cross.property
    · exact congrArg Subtype.val hc₀
    · exact congrArg (fun x => x.2.2) htop
  have hL : D.left₂ = E.left₂ := by
    apply Subtype.ext
    apply ext_source_top D.left₂.property E.left₂.property
    · change M.nu.source 1 D.left₂.val = M.nu.source 1 E.left₂.val
      rw [D.left_source, E.left_source, hl, hc]
    · exact congrArg Prod.fst htop
  have hR : D.right₂ = E.right₂ := by
    apply Subtype.ext
    apply ext_source_top D.right₂.property E.right₂.property
    · exact hR₀
    · exact congrArg (fun x => x.2.1) htop
  have hl'' : D.left = E.left := Subtype.ext hl
  have hr'' : D.right = E.right := Subtype.ext hr'
  cases D
  cases E
  cases hl''
  cases hc
  cases hr''
  cases hL
  cases hR
  rfl

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
open CylinderTables

variable {M : DirectedComplex.{u}}
namespace CrossingSquare

def ofTable (hM : PositiveAcyclic M) (t : M.cylinder.nu.Cells 2)
    (hs : label t.val false = 0) (ht : label t.val true = 1) : CrossingSquare M.nu where
  left := ⟨profileEdge t.val hs ht false false, profileEdge_bounded _ _ _ _ _⟩
  cross := ⟨crossingProfile t.val hs ht, crossingProfile_bounded _ _ _ t.property⟩
  right := ⟨profileEdge t.val hs ht true true, profileEdge_bounded _ _ _ _ _⟩
  left₂ := ⟨leftProfile t.val hs ht, leftProfile_bounded _ _ _ t.property⟩
  right₂ := ⟨rightProfile t.val hs ht, rightProfile_bounded _ _ _ t.property⟩
  lc := truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1
  cr := (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm
  left_source := by
    apply ext_source_top (M.nu.source_source_self 1 _) (composite_bounded M.nu (by omega : 0 < 1)
      _ _ (profileEdge_bounded _ _ _ _ _) (crossingProfile_bounded _ _ _ t.property)
      (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1))
    · change truncate 0 false (truncate 1 false _) = M.nu.source 0 (M.nu.join 0 _ _)
      rw [M.nu.join_source_le 0 0 _ _ le_rfl
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1)]
      apply truncate_zero_ext
      change (leftProfile t.val hs ht).row 0 false = (profileEdge t.val hs ht false false).row 0 false
      erw [profile_left_zero hM]
    · erw [table_join_zero_row_succ _ _
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).1),
        profileEdge_one]
      change side t.val false 1 false + CylinderTables.cross t.val 1 false =
        side t.val false 1 false + CylinderTables.cross t.val 1 false
      rfl
  right_target := by
    apply ext_source_top (M.nu.source_target_self 1 _) (composite_bounded M.nu (by omega : 0 < 1)
      _ _ (crossingProfile_bounded _ _ _ t.property) (profileEdge_bounded _ _ _ _ _)
      (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm)
    · change truncate 0 false (truncate 1 true _) = M.nu.source 0 (M.nu.join 0 _ _)
      rw [M.nu.join_source_le 0 0 _ _ le_rfl
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm]
      apply truncate_zero_ext
      change (rightProfile t.val hs ht).row 0 false = (crossingProfile t.val hs ht).row 0 false
      erw [profile_right_zero hM]
      simp only [Bool.false_eq_true, ite_false]
      rfl
    · erw [table_join_zero_row_succ _ _
        (truncate_zero_ext _ _ _ _ (twoMiddle_matches hM t.val hs ht).2).symm,
        profileEdge_one]
      change side t.val true 1 true + CylinderTables.cross t.val 1 true =
        CylinderTables.cross t.val 1 false + side t.val true 1 true
      have hc : CylinderTables.cross t.val 1 false = CylinderTables.cross t.val 1 true :=
        row_top_fixed _ (crossingProfile_bounded t.val hs ht t.property)
      rw [hc]
      exact add_comm _ _

lemma image_ofTable (hM : PositiveAcyclic M) (t : M.cylinder.nu.Cells 2)
    (hs : label t.val false = 0) (ht : label t.val true = 1) :
    (chainComparison M).map (ofTable hM t hs ht).value = t.val := by
  let D := ofTable hM t hs ht
  have hR : (chainComparison M).map D.first = twoRight t.val hs ht := D.image_first
  have hC : (chainComparison M).map D.middle = twoMiddle t.val hs ht := D.image_middle
  have hL : (chainComparison M).map D.last = twoLeft t.val hs ht := D.image_last
  change (chainComparison M).map D.value = _
  rw [value, (chainComparison M).map_join 1 _ _ D.firstMiddle_last,
    (chainComparison M).map_join 1 _ _ D.first_middle, hR, hC, hL,
    M.cylinder.nu.join_eq 1 _ _ (twoRightMiddle_match hM t.val hs ht t.property)]
  erw [M.cylinder.nu.join_eq 1 _ _ (twoRightMiddleLeft_match hM t.val hs ht t.property)]
  exact crossing_two_factor hM t.val hs ht t.property

theorem unique_ofTable (hM : PositiveAcyclic M) (t : M.cylinder.nu.Cells 2)
    (hs : label t.val false = 0) (ht : label t.val true = 1) :
    ∃! D : CrossingSquare M.nu, (chainComparison M).map D.value = t.val := by
  refine ⟨ofTable hM t hs ht, image_ofTable hM t hs ht, ?_⟩
  intro D hD
  exact D.image_ext _ (hD.trans (image_ofTable hM t hs ht).symm)

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X : OmegaCategory.{u}}

lemma crossingEdge_comp_right (l : X.Cells 1) (c : X.Objects) (r s : X.Cell)
    (hl : X.target 0 l.val = c.val) (hr : X.source 0 r = c.val)
    (hs : X.source 0 s = c.val) (h : X.target 1 r = X.source 1 s) :
    crossingEdge l.val c (X.join 1 r s) =
      (tensorFunctor.obj X).join 1 (crossingEdge l.val c r) (crossingEdge l.val c s) := by
  unfold crossingEdge
  erw [((tensorEndpoint true).app X).map_join 1 r s h]
  apply (tensorFunctor.obj X).join_whisker_left 0 1 (by omega)
  · apply composite_bounded _ (by omega : 0 < 1) _ _ _
      (verticalObject_bounded c) (crossingEdge_left_matching l.val c hl)
    rw [endpoint_source, l.property]
  · exact ((tensorEndpoint true).app X).map_composable h
  · exact crossingEdge_right_matching l.val c r hl hr
  · exact crossingEdge_right_matching l.val c s hl hs

lemma crossingEdge_comp_left (l s : X.Cell) (c : X.Objects) (r : X.Cells 1)
    (hl : X.target 0 l = c.val) (hs : X.target 0 s = c.val)
    (hr : X.source 0 r.val = c.val) (h : X.target 1 l = X.source 1 s) :
    crossingEdge (X.join 1 l s) c r.val =
      (tensorFunctor.obj X).join 1 (crossingEdge l c r.val) (crossingEdge s c r.val) := by
  unfold crossingEdge
  erw [((tensorEndpoint false).app X).map_join 1 l s h,
    (tensorFunctor.obj X).join_whisker_right 0 1 (by omega) _ _ _
      (verticalObject_bounded c) (((tensorEndpoint false).app X).map_composable h)
      (crossingEdge_left_matching l c hl) (crossingEdge_left_matching s c hs)]
  apply (tensorFunctor.obj X).join_whisker_right 0 1 (by omega)
  · rw [endpoint_source, r.property]
  · rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
        (crossingEdge_left_matching l c hl),
      (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
        (crossingEdge_left_matching s c hs), endpoint_target, endpoint_source,
      h, verticalObject_bounded,
      (tensorFunctor.obj X).target_eq_self_of_source_eq_self (verticalObject_bounded c)]
  · exact crossingEdge_right_matching l c r.val hl hr
  · exact crossingEdge_right_matching s c r.val hs hr

lemma crossingEdge_middle (l r : X.Cell) (c : X.Objects)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).join 1
      (crossingEdge l c (X.source 1 r)) (crossingEdge (X.target 1 l) c r) =
    (tensorFunctor.obj X).join 1
      (crossingEdge (X.source 1 l) c r) (crossingEdge l c (X.target 1 r)) := by
  have h := (tensorFunctor.obj X).join_middle 0 1 (by omega)
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalObject c))
    (((tensorEndpoint true).app X).map r) (crossingEdge_right_matching l c r hl hr)
  rw [(tensorFunctor.obj X).join_target_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl),
    (tensorFunctor.obj X).join_source_gt 1 0 _ _ (by omega)
      (crossingEdge_left_matching l c hl), endpoint_target, endpoint_source,
    endpoint_target, endpoint_source, verticalObject_bounded,
    (tensorFunctor.obj X).target_eq_self_of_source_eq_self (verticalObject_bounded c)] at h
  exact h

def whiskeredVertical (l : X.Cell) (c : X.Cells 1) (r : X.Cell) : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalCell 1 c))
    (((tensorEndpoint true).app X).map r)

lemma whiskeredVertical_left_match (l : X.Cell) (c : X.Cells 1)
    (hl : X.target 0 l = X.source 0 c.val) :
    (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map l) =
      (tensorFunctor.obj X).source 0 (verticalCell 1 c) := by
  rw [endpoint_target, CrossingSquare.vertical_source_zero, hl]

lemma whiskeredVertical_right_match (l : X.Cell) (c : X.Cells 1) (r : X.Cell)
    (hl : X.target 0 l = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r) :
    (tensorFunctor.obj X).target 0
      ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalCell 1 c)) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map r) := by
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl (whiskeredVertical_left_match l c hl),
    CrossingSquare.vertical_target_zero, endpoint_source, hr]

lemma whiskeredVertical_source (l : X.Cells 1) (c : X.Cells 1) (r : X.Cells 1)
    (hl : X.target 0 l.val = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r.val) :
    (tensorFunctor.obj X).source 1 (whiskeredVertical l.val c r.val) =
      crossingEdge l.val ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r.val) := by
  let D : CrossingSquare X :=
    { left := l, cross := c, right := r
      left₂ := ⟨X.join 0 l.val c.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl)⟩
      right₂ := ⟨X.join 0 c.val r.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr)⟩
      lc := hl, cr := hr
      left_source := composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl
      right_target := X.target_eq_self_of_source_eq_self
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr) }
  exact D.middle_source

lemma whiskeredVertical_target (l : X.Cells 1) (c : X.Cells 1) (r : X.Cells 1)
    (hl : X.target 0 l.val = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r.val) :
    (tensorFunctor.obj X).target 1 (whiskeredVertical l.val c r.val) =
      crossingEdge (X.join 0 l.val c.val) ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r.val := by
  let D : CrossingSquare X :=
    { left := l, cross := c, right := r
      left₂ := ⟨X.join 0 l.val c.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl)⟩
      right₂ := ⟨X.join 0 c.val r.val, X.source_fixed_upwards (by omega : 1 ≤ 2)
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr)⟩
      lc := hl, cr := hr
      left_source := composite_bounded X (by omega : 0 < 1) _ _ l.property c.property hl
      right_target := X.target_eq_self_of_source_eq_self
        (composite_bounded X (by omega : 0 < 1) _ _ c.property r.property hr) }
  exact D.middle_target

lemma verticalCell_one_source (c : X.Cells 1) :
    (tensorFunctor.obj X).source 1 (verticalCell 1 c) =
      (tensorFunctor.obj X).join 0
        (verticalObject ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩)
        (((tensorEndpoint true).app X).map c.val) := verticalCell_one_face c false

lemma verticalCell_one_target (c : X.Cells 1) :
    (tensorFunctor.obj X).target 1 (verticalCell 1 c) =
      (tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map c.val)
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩) := verticalCell_one_face c true

lemma whiskeredVertical_comp (l c d r : X.Cells 1)
    (hl : X.target 0 l.val = X.source 0 c.val)
    (hc : X.target 0 c.val = X.source 0 d.val)
    (hr : X.target 0 d.val = X.source 0 r.val) :
    whiskeredVertical l.val (X.gradedComp (by omega : 0 < 1) c d hc) r.val =
      (tensorFunctor.obj X).join 1
        (whiskeredVertical l.val c (X.join 0 d.val r.val))
        (whiskeredVertical (X.join 0 l.val c.val) d r.val) := by
  let T := tensorFunctor.obj X
  let E₀ := (tensorEndpoint false).app X
  let E₁ := (tensorEndpoint true).app X
  have hcad : T.target 0 (verticalCell 1 c) = T.source 0 (E₁.map d.val) := by
    rw [CrossingSquare.vertical_target_zero, endpoint_source, hc]
  have hcb : T.target 0 (E₀.map c.val) = T.source 0 (verticalCell 1 d) := by
    rw [endpoint_target, CrossingSquare.vertical_source_zero, hc]
  let A := T.join 0 (verticalCell 1 c) (E₁.map d.val)
  let B := T.join 0 (E₀.map c.val) (verticalCell 1 d)
  have ha : T.target 1 A = T.source 1 B := by
    dsimp [A,B]
    rw [T.join_target_gt 1 0 _ _ (by omega) hcad,
      T.join_source_gt 1 0 _ _ (by omega) hcb,
      verticalCell_one_target, verticalCell_one_source,
      endpoint_target, endpoint_source,
      X.target_eq_self_of_source_eq_self d.property, c.property]
    have he : (⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ : X.Objects) =
        ⟨X.source 0 d.val, X.source_source_self 0 d.val⟩ := Subtype.ext hc
    rw [he]
    apply T.join_assoc
    · erw [verticalObject_source, endpoint_target, hc]
    · erw [verticalObject_target, endpoint_source]
  have hla : T.target 0 (E₀.map l.val) = T.source 0 A := by
    rw [show A = T.join 0 (verticalCell 1 c) (E₁.map d.val) from rfl,
      T.join_source_le 0 0 _ _ le_rfl hcad]
    exact whiskeredVertical_left_match l.val c hl
  have hlb : T.target 0 (E₀.map l.val) = T.source 0 B := by
    rw [show B = T.join 0 (E₀.map c.val) (verticalCell 1 d) from rfl,
      T.join_source_le 0 0 _ _ le_rfl hcb, endpoint_target, endpoint_source, hl]
  have hlfix : T.source 1 (E₀.map l.val) = E₀.map l.val := by rw [endpoint_source,l.property]
  have hrfix : T.source 1 (E₁.map r.val) = E₁.map r.val := by rw [endpoint_source,r.property]
  have hlar : T.target 0 (T.join 0 (E₀.map l.val) A) = T.source 0 (E₁.map r.val) := by
    rw [T.join_target_le 0 0 _ _ le_rfl hla,
      show A = T.join 0 (verticalCell 1 c) (E₁.map d.val) from rfl,
      T.join_target_le 0 0 _ _ le_rfl hcad, endpoint_target, endpoint_source, hr]
  have hlbr : T.target 0 (T.join 0 (E₀.map l.val) B) = T.source 0 (E₁.map r.val) := by
    rw [T.join_target_le 0 0 _ _ le_rfl hlb,
      show B = T.join 0 (E₀.map c.val) (verticalCell 1 d) from rfl,
      T.join_target_le 0 0 _ _ le_rfl hcb,
      CrossingSquare.vertical_target_zero, endpoint_source, hr]
  have hab : T.target 1 (T.join 0 (E₀.map l.val) A) = T.source 1 (T.join 0 (E₀.map l.val) B) := by
    rw [T.join_target_gt 1 0 _ _ (by omega) hla,
      T.join_source_gt 1 0 _ _ (by omega) hlb,
      T.target_eq_self_of_source_eq_self hlfix, hlfix, ha]
  unfold whiskeredVertical
  rw [verticalCell_one_comp]
  change T.join 0 (T.join 0 (E₀.map l.val) (T.join 1 A B)) (E₁.map r.val) = _
  rw [T.join_whisker_left 0 1 (by omega) _ _ _ hlfix ha hla hlb,
    T.join_whisker_right 0 1 (by omega) _ _ _ hrfix hab hlar hlbr]
  have he₁ : T.join 0 (T.join 0 (E₀.map l.val) A) (E₁.map r.val) =
      T.join 0 (T.join 0 (E₀.map l.val) (verticalCell 1 c)) (E₁.map (X.join 0 d.val r.val)) := by
    dsimp [A]
    erw [E₁.map_join 0 _ _ hr]
    rw [← T.join_assoc 0 _ _ _ (whiskeredVertical_left_match l.val c hl) hcad,
      T.join_assoc 0 _ _ _ (whiskeredVertical_right_match l.val c d.val hl hc)
        (E₁.map_composable hr)]
  have he₂ : T.join 0 (T.join 0 (E₀.map l.val) B) (E₁.map r.val) =
      T.join 0 (T.join 0 (E₀.map (X.join 0 l.val c.val)) (verticalCell 1 d)) (E₁.map r.val) := by
    dsimp [B]
    erw [E₀.map_join 0 _ _ hl]
    rw [T.join_assoc 0 _ _ _ (E₀.map_composable hl) hcb]
  rw [he₁,he₂]

lemma whiskeredVertical_exchange_right (l c : X.Cells 1) (r : X.Cell)
    (hl : X.target 0 l.val = X.source 0 c.val)
    (hr : X.target 0 c.val = X.source 0 r) :
    (tensorFunctor.obj X).join 1
      (whiskeredVertical l.val c (X.source 1 r))
      (crossingEdge (X.join 0 l.val c.val)
        ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r) =
    (tensorFunctor.obj X).join 1
      (crossingEdge l.val ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r))
      (whiskeredVertical l.val c (X.target 1 r)) := by
  let T := tensorFunctor.obj X
  let E₀ := (tensorEndpoint false).app X
  let E₁ := (tensorEndpoint true).app X
  have h := T.join_middle 0 1 (by omega)
    (T.join 0 (E₀.map l.val) (verticalCell 1 c)) (E₁.map r)
    (whiskeredVertical_right_match l.val c r hl hr)
  rw [T.join_source_gt 1 0 _ _ (by omega) (whiskeredVertical_left_match l.val c hl),
    T.join_target_gt 1 0 _ _ (by omega) (whiskeredVertical_left_match l.val c hl),
    endpoint_source, endpoint_source, endpoint_target, endpoint_target,
    l.property, X.target_eq_self_of_source_eq_self l.property,
    verticalCell_one_source, verticalCell_one_target] at h
  have hem : T.target 0 (E₀.map c.val) = T.source 0
      (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩) := by
    erw [endpoint_target, verticalObject_source]
  rw [← T.join_assoc 0 _ _ _ (E₀.map_composable hl) hem] at h
  erw [← E₀.map_join 0 _ _ hl] at h
  have hmv : T.target 0
      (verticalObject ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩) =
      T.source 0 (E₁.map c.val) := by erw [verticalObject_target, endpoint_source]
  erw [← T.join_assoc 0 _ _ _ (crossingEdge_left_matching l.val _ hl) hmv,
    T.join_assoc 0 _ _ _ (crossingEdge_right_matching l.val _ c.val hl rfl)
      (E₁.map_composable hr)] at h
  erw [← E₁.map_join 0 _ _ hr] at h
  exact h

lemma whiskeredVertical_exchange_left (l : X.Cell) (c r : X.Cells 1)
    (hl : X.target 0 l = X.source 0 c.val)
    (hr : X.target 0 c.val = X.source 0 r.val) :
    (tensorFunctor.obj X).join 1
      (crossingEdge l ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r.val))
      (whiskeredVertical (X.target 1 l) c r.val) =
    (tensorFunctor.obj X).join 1
      (whiskeredVertical (X.source 1 l) c r.val)
      (crossingEdge (X.join 0 l c.val)
        ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r.val) := by
  let T := tensorFunctor.obj X
  let E₀ := (tensorEndpoint false).app X
  let E₁ := (tensorEndpoint true).app X
  have hcr : T.target 0 (verticalCell 1 c) = T.source 0 (E₁.map r.val) := by
    rw [CrossingSquare.vertical_target_zero, endpoint_source, hr]
  have hlt : T.target 0 (E₀.map l) = T.source 0 (T.join 0 (verticalCell 1 c) (E₁.map r.val)) := by
    rw [T.join_source_le 0 0 _ _ le_rfl hcr]
    exact whiskeredVertical_left_match l c hl
  have h := T.join_middle 0 1 (by omega) (E₀.map l)
    (T.join 0 (verticalCell 1 c) (E₁.map r.val)) hlt
  rw [T.join_source_gt 1 0 _ _ (by omega) hcr,
    T.join_target_gt 1 0 _ _ (by omega) hcr,
    endpoint_source, endpoint_source, endpoint_target, endpoint_target,
    r.property, X.target_eq_self_of_source_eq_self r.property,
    verticalCell_one_source, verticalCell_one_target] at h
  have hl' : X.target 0 (X.source 1 l) = X.source 0 c.val := by
    rw [X.target_source, ite_eq_left (by omega : 0 < 1)]; exact hl
  have hl'' : X.target 0 (X.target 1 l) = X.source 0 c.val := by
    rw [X.target_target, min_eq_left (by omega : 0 ≤ 1)]; exact hl
  rw [← T.join_assoc 0 _ _ _ (whiskeredVertical_left_match _ c hl') hcr,
    ← T.join_assoc 0 _ _ _ (whiskeredVertical_left_match _ c hl'') hcr] at h
  have hsrc : T.join 0 (E₀.map l)
      (T.join 0 (T.join 0 (verticalObject ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩)
        (E₁.map c.val)) (E₁.map r.val)) =
      crossingEdge l ⟨X.source 0 c.val, X.source_source_self 0 c.val⟩ (X.join 0 c.val r.val) := by
    unfold crossingEdge
    erw [T.join_assoc 0 _ _ _ (by erw [verticalObject_target, endpoint_source]) (E₁.map_composable hr),
      ← T.join_assoc 0 _ _ _ (crossingEdge_left_matching l _ hl) (by
        erw [← E₁.map_join 0 _ _ hr]
        erw [verticalObject_target, endpoint_source, X.join_source_le 0 0 _ _ le_rfl hr])]
    erw [E₁.map_join 0 _ _ hr]
  have htgt : T.join 0 (E₀.map l)
      (T.join 0 (T.join 0 (E₀.map c.val)
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩)) (E₁.map r.val)) =
      crossingEdge (X.join 0 l c.val)
        ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩ r.val := by
    unfold crossingEdge
    have h₁ : T.target 0 (E₀.map c.val) = T.source 0
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩) := by
      erw [endpoint_target, verticalObject_source]
    have h₂ : T.target 0 (T.join 0 (E₀.map c.val)
        (verticalObject ⟨X.target 0 c.val, X.source_target_self 0 c.val⟩)) =
        T.source 0 (E₁.map r.val) := crossingEdge_right_matching c.val _ r.val rfl hr.symm
    rw [← T.join_assoc 0 _ _ _ (by
        rw [T.join_source_le 0 0 _ _ le_rfl h₁, endpoint_source, endpoint_target, hl]) h₂,
      ← T.join_assoc 0 _ _ _ (E₀.map_composable hl) h₁]
    erw [E₀.map_join 0 _ _ hl]
  rw [hsrc,htgt] at h
  exact h
end Thomason.GrayRecursive.IntervalHom

end

end OAI
