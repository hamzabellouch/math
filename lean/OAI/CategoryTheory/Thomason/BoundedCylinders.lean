import Mathlib
import OAI.CategoryTheory.Thomason.EdgeComparison

namespace OAI

/-! Bounded Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma truncate_zero_ext (x y : Table M) (a b : Bool)
    (h : x.row 0 a = y.row 0 b) : truncate 0 a x = truncate 0 b y := by
  ext p e
  cases p with
  | zero => exact h
  | succ p => rfl

lemma truncate_one_ext (x y : Table M) (a b : Bool)
    (h₀ : ∀ e, x.row 0 e = y.row 0 e) (h₁ : x.row 1 a = y.row 1 b) :
    truncate 1 a x = truncate 1 b y := by
  ext p e
  cases p with
  | zero => exact h₀ e
  | succ p => cases p with
    | zero => exact h₁
    | succ p => rfl

def tableSandwich (l c r : Table M) : Table M.cylinder :=
  M.cylinder.nu.join 0
    (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l) (verticalTable c))
    ((M.cylinderEndpoint true).table r)

lemma tableSandwich_match_left (l c : Table M) (hl : l.row 0 true = c.row 0 false) :
    truncate 0 true ((M.cylinderEndpoint false).table l) = truncate 0 false (verticalTable c) := by
  apply truncate_zero_ext
  change (l.row 0 true, 0) = (c.row 0 false, 0)
  rw [hl]

lemma tableSandwich_match_right (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true) :
    truncate 0 true (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l) (verticalTable c)) =
      truncate 0 false ((M.cylinderEndpoint true).table r) := by
  apply (M.cylinder.nu.join_target_le 0 0 _ _ le_rfl (tableSandwich_match_left l c hl)).trans
  apply truncate_zero_ext
  change (0, c.row 0 true) = (0, r.row 0 false)
  rw [hr]

lemma tableSandwich_zero (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true) (b : Bool) :
    (tableSandwich l c r).row 0 b = if b then (0,r.row 0 true) else (l.row 0 false,0) := by
  unfold tableSandwich
  rw [GrayRecursive.IntervalHom.table_join_zero_row_zero _ _ (tableSandwich_match_right l c r hl hr),
      GrayRecursive.IntervalHom.table_join_zero_row_zero _ _ (tableSandwich_match_left l c hl)]
  cases b <;> rfl

lemma tableSandwich_succ (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true)
    (p : ℕ) (b : Bool) :
    (tableSandwich l c r).row (p+1) b =
      M.cylinderEndpointMap false (p+1) (l.row (p+1) b) + verticalRow c (p+1) b +
      M.cylinderEndpointMap true (p+1) (r.row (p+1) b) := by
  unfold tableSandwich
  rw [GrayRecursive.IntervalHom.table_join_zero_row_succ _ _ (tableSandwich_match_right l c r hl hr),
      GrayRecursive.IntervalHom.table_join_zero_row_succ _ _ (tableSandwich_match_left l c hl)]
  rfl

lemma tableSandwich_bounded (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true)
    (hdl : truncate 2 false l = l) (hdc : truncate 1 false c = c) (hdr : truncate 2 false r = r) :
    truncate 2 false (tableSandwich l c r) = tableSandwich l c r := by
  have heL : M.cylinder.nu.source 2 ((M.cylinderEndpoint false).table l) =
      (M.cylinderEndpoint false).table l := by
    change truncate 2 false _ = _
    rw [← Hom.table_truncate, hdl]
  have heR : M.cylinder.nu.source 2 ((M.cylinderEndpoint true).table r) =
      (M.cylinderEndpoint true).table r := by
    change truncate 2 false _ = _
    rw [← Hom.table_truncate, hdr]
  exact GrayRecursive.IntervalHom.composite_bounded M.cylinder.nu (by omega : 0 < 2) _ _
    (GrayRecursive.IntervalHom.composite_bounded M.cylinder.nu (by omega : 0 < 2) _ _
      heL (GrayRecursive.vertical_fixed c hdc) (tableSandwich_match_left l c hl))
    heR (tableSandwich_match_right l c r hl hr)

lemma crossingProfile_face_zero (t : Table M.cylinder) (hs : label t false = 0)
    (ht : label t true = 1) (b : Bool) :
    (crossingProfile t hs ht).row 0 b = cross t 0 b := rfl

lemma profile_left_zero (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (b : Bool) :
    (leftProfile t hs ht).row 0 b = if b then cross t 0 true else side t false 0 false := by
  obtain ⟨_,htgt⟩ := crossing_starts_ends hM t hs ht
  cases b <;> simp only [leftProfile, leftProfileRow, Even.zero, Bool.false_eq_true,
    ite_false, ite_true, add_zero, htgt, zero_add]

lemma profile_right_zero (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (b : Bool) :
    (rightProfile t hs ht).row 0 b = if b then side t true 0 true else cross t 0 false := by
  obtain ⟨hsrc,_⟩ := crossing_starts_ends hM t hs ht
  cases b <;> simp only [rightProfile, rightProfileRow, Even.zero, Bool.false_eq_true,
    ite_false, ite_true, add_zero, hsrc, zero_add]

lemma face_one_label (t : Table M.cylinder) (a b : Bool) :
    label (truncate 1 a t) b = label t b := rfl

def profileEdge (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (a b : Bool) : Table M :=
  if a then rightProfile (truncate 1 b t) hs ht else leftProfile (truncate 1 b t) hs ht

lemma profileEdge_bounded (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (a b : Bool) : truncate 1 false (profileEdge t hs ht a b) = profileEdge t hs ht a b := by
  have h : truncate 1 false (truncate 1 b t) = truncate 1 b t := by simp only [truncate_truncate, lt_self_iff_false, ite_false]
  cases a
  · exact leftProfile_bounded (truncate 1 b t) hs ht h
  · exact rightProfile_bounded (truncate 1 b t) hs ht h

lemma profileEdge_zero (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (a b e : Bool) :
    (profileEdge t hs ht a b).row 0 e =
      if a then (if e then side t true 0 true else cross t 0 b)
      else (if e then cross t 0 b else side t false 0 false) := by
  cases a
  · change (leftProfile (truncate 1 b t) hs ht).row 0 e = _
    erw [profile_left_zero hM]
    cases e <;> rfl
  · change (rightProfile (truncate 1 b t) hs ht).row 0 e = _
    erw [profile_right_zero hM]
    cases e <;> rfl

lemma profileEdge_one (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (a b e : Bool) : (profileEdge t hs ht a b).row 1 e = side t a 1 b := by
  cases a <;> cases e <;>
    change _ + (0 : M.Chain 1) = _ <;> exact add_zero _

section TwoCell
variable (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)

def twoRight : Table M.cylinder := tableSandwich (profileEdge t hs ht false false)
  (truncate 0 false (crossingProfile t hs ht)) (rightProfile t hs ht)

def twoMiddle : Table M.cylinder := tableSandwich (profileEdge t hs ht false false)
  (crossingProfile t hs ht) (profileEdge t hs ht true true)

def twoLeft : Table M.cylinder := tableSandwich (leftProfile t hs ht)
  (truncate 0 true (crossingProfile t hs ht)) (profileEdge t hs ht true true)

include hM

lemma twoRight_matches :
    (profileEdge t hs ht false false).row 0 true = (truncate 0 false (crossingProfile t hs ht)).row 0 false ∧
    (rightProfile t hs ht).row 0 false = (truncate 0 false (crossingProfile t hs ht)).row 0 true := by
  simp only [profileEdge_zero hM, profile_right_zero hM, Bool.false_eq_true, ite_false, ite_true,
    truncate_top_row, crossingProfile_face_zero, and_self]

lemma twoMiddle_matches :
    (profileEdge t hs ht false false).row 0 true = (crossingProfile t hs ht).row 0 false ∧
    (profileEdge t hs ht true true).row 0 false = (crossingProfile t hs ht).row 0 true := by
  simp only [profileEdge_zero hM, Bool.false_eq_true, ite_false, ite_true,
    crossingProfile_face_zero, and_self]

lemma twoLeft_matches :
    (leftProfile t hs ht).row 0 true = (truncate 0 true (crossingProfile t hs ht)).row 0 false ∧
    (profileEdge t hs ht true true).row 0 false = (truncate 0 true (crossingProfile t hs ht)).row 0 true := by
  simp only [profile_left_zero hM, profileEdge_zero hM, Bool.false_eq_true, ite_false, ite_true,
    truncate_top_row, crossingProfile_face_zero, and_self]

lemma twoRight_zero (b : Bool) : (twoRight t hs ht).row 0 b = t.row 0 b := by
  obtain ⟨hsrc, htgt⟩ := crossing_starts_ends hM t hs ht
  rw [twoRight, tableSandwich_zero _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2,
    profile_right_zero hM, profileEdge_zero hM]
  cases b
  · exact Prod.ext rfl hsrc.symm
  · exact Prod.ext htgt.symm rfl

lemma twoMiddle_zero (b : Bool) : (twoMiddle t hs ht).row 0 b = t.row 0 b := by
  obtain ⟨hsrc, htgt⟩ := crossing_starts_ends hM t hs ht
  rw [twoMiddle, tableSandwich_zero _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2,
    profileEdge_zero hM, profileEdge_zero hM]
  cases b
  · exact Prod.ext rfl hsrc.symm
  · exact Prod.ext htgt.symm rfl

lemma twoLeft_zero (b : Bool) : (twoLeft t hs ht).row 0 b = t.row 0 b := by
  obtain ⟨hsrc, htgt⟩ := crossing_starts_ends hM t hs ht
  rw [twoLeft, tableSandwich_zero _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2,
    profileEdge_zero hM, profile_left_zero hM]
  cases b
  · exact Prod.ext rfl hsrc.symm
  · exact Prod.ext htgt.symm rfl

lemma twoRight_one (b : Bool) : (twoRight t hs ht).row 1 b =
    (side t false 1 false,
      side t true 1 b + (if b then cross t 1 true else 0), cross t 0 false) := by
  rw [twoRight, tableSandwich_succ _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2,
    profileEdge_one]
  cases b <;>
    simp [verticalRow, truncate_row, rightProfile, rightProfileRow, crossingProfile,
      cylinderEndpointMap]

lemma twoMiddle_one (b : Bool) : (twoMiddle t hs ht).row 1 b =
    (side t false 1 false + (if b then cross t 1 true else 0),
      (if b then 0 else cross t 1 false) + side t true 1 true, cross t 0 b) := by
  rw [twoMiddle, tableSandwich_succ _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2,
    profileEdge_one, profileEdge_one]
  cases b <;> simp [verticalRow, crossingProfile, cylinderEndpointMap]

lemma twoLeft_one (b : Bool) : (twoLeft t hs ht).row 1 b =
    (side t false 1 b + (if b then 0 else cross t 1 false), side t true 1 true, cross t 0 true) := by
  rw [twoLeft, tableSandwich_succ _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2,
    profileEdge_one]
  cases b <;>
    simp [verticalRow, truncate_row, leftProfile, leftProfileRow, crossingProfile,
      cylinderEndpointMap]

variable (hb : truncate 2 false t = t)
include hb

omit hM in
lemma profileCross_two_zero (b : Bool) : cross t 2 b = 0 :=
  cross_of_row_zero t 2 b (row_above_fixed t hb (by omega) b)

lemma twoRight_two (b : Bool) : (twoRight t hs ht).row 2 b = (0,side t true 2 b,0) := by
  rw [twoRight, tableSandwich_succ _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2]
  have hl := row_above_fixed _ (profileEdge_bounded t hs ht false false) (by omega : 1 < 2) b
  have hc := profileCross_two_zero t hb b
  simp only [hl, map_zero]
  change (0 : M.cylinder.Chain 2) + verticalRow _ 2 b +
    M.cylinderEndpointMap true 2 (rightProfileRow t 2 b) = _
  cases b <;>
    simp [verticalRow, truncate_row, rightProfileRow, hc, cylinderEndpointMap]

lemma twoMiddle_two (b : Bool) : (twoMiddle t hs ht).row 2 b = (0,0,cross t 1 b) := by
  rw [twoMiddle, tableSandwich_succ _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2]
  have hl := row_above_fixed _ (profileEdge_bounded t hs ht false false) (by omega : 1 < 2) b
  have hr := row_above_fixed _ (profileEdge_bounded t hs ht true true) (by omega : 1 < 2) b
  simp only [hl, hr, map_zero, zero_add, add_zero]
  change verticalRow (crossingProfile t hs ht) 2 b = _
  have hc := profileCross_two_zero t hb b
  cases b <;> simp [verticalRow, crossingProfile, hc]

lemma twoLeft_two (b : Bool) : (twoLeft t hs ht).row 2 b = (side t false 2 b,0,0) := by
  rw [twoLeft, tableSandwich_succ _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2]
  have hr := row_above_fixed _ (profileEdge_bounded t hs ht true true) (by omega : 1 < 2) b
  have hc := profileCross_two_zero t hb b
  simp only [hr, map_zero, add_zero]
  change M.cylinderEndpointMap false 2 (leftProfileRow t 2 b) + verticalRow _ 2 b = _
  cases b <;> simp [verticalRow, truncate_row, leftProfileRow, hc, cylinderEndpointMap]

omit hM hb in
lemma profileEdge_bounded_two (_hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (_hb : truncate 2 false t = t) (a b : Bool) :
    truncate 2 false (profileEdge t hs ht a b) = profileEdge t hs ht a b :=
  M.nu.source_fixed_upwards (by omega : 1 ≤ 2) (profileEdge_bounded t hs ht a b)

lemma twoRight_bounded : truncate 2 false (twoRight t hs ht) = twoRight t hs ht :=
  tableSandwich_bounded _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2
    (profileEdge_bounded_two hM t hs ht hb false false)
    (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false])
    (rightProfile_bounded t hs ht hb)

lemma twoMiddle_bounded : truncate 2 false (twoMiddle t hs ht) = twoMiddle t hs ht :=
  tableSandwich_bounded _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2
    (profileEdge_bounded_two hM t hs ht hb false false) (crossingProfile_bounded t hs ht hb)
    (profileEdge_bounded_two hM t hs ht hb true true)

lemma twoLeft_bounded : truncate 2 false (twoLeft t hs ht) = twoLeft t hs ht :=
  tableSandwich_bounded _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2
    (leftProfile_bounded t hs ht hb)
    (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false])
    (profileEdge_bounded_two hM t hs ht hb true true)

omit hM hb in
lemma twoRight_source (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (_hb : truncate 2 false t = t) :
    truncate 1 false (twoRight t hs ht) = truncate 1 false t := by
  apply truncate_one_ext
  · exact twoRight_zero hM t hs ht
  · rw [twoRight_one hM t hs ht]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    rfl

lemma twoRightMiddle_match : truncate 1 true (twoRight t hs ht) = truncate 1 false (twoMiddle t hs ht) := by
  have he : cross t 1 false = cross t 1 true :=
    congrArg (fun z => z.2.2) (row_top_fixed t hb)
  apply truncate_one_ext
  · intro e
    rw [twoRight_zero hM t hs ht, twoMiddle_zero hM t hs ht]
  · rw [twoRight_one hM t hs ht, twoMiddle_one hM t hs ht]
    simp only [ite_true, Bool.false_eq_true, ite_false, add_zero, he, add_comm]

lemma twoMiddleLeft_match : truncate 1 true (twoMiddle t hs ht) = truncate 1 false (twoLeft t hs ht) := by
  have he : cross t 1 false = cross t 1 true :=
    congrArg (fun z => z.2.2) (row_top_fixed t hb)
  apply truncate_one_ext
  · intro e
    rw [twoMiddle_zero hM t hs ht, twoLeft_zero hM t hs ht]
  · rw [twoMiddle_one hM t hs ht, twoLeft_one hM t hs ht]
    simp only [ite_true, Bool.false_eq_true, ite_false, zero_add, he]

lemma twoRightMiddleLeft_match : truncate 1 true
    (comp 1 (twoRight t hs ht) (twoMiddle t hs ht) (twoRightMiddle_match hM t hs ht hb)) =
      truncate 1 false (twoLeft t hs ht) := by
  rw [target_comp_le 1 1 le_rfl]
  exact twoMiddleLeft_match hM t hs ht hb

lemma crossing_two_factor :
    comp 1 (comp 1 (twoRight t hs ht) (twoMiddle t hs ht) (twoRightMiddle_match hM t hs ht hb))
      (twoLeft t hs ht) (twoRightMiddleLeft_match hM t hs ht hb) = t := by
  apply ext_source_top (comp_dimension (by omega : 1 < 2)
    (comp_dimension (by omega : 1 < 2) (twoRight_bounded hM t hs ht hb)
      (twoMiddle_bounded hM t hs ht hb) _) (twoLeft_bounded hM t hs ht hb) _) hb
  · rw [source_comp_le 1 1 le_rfl, source_comp_le 1 1 le_rfl]
    exact twoRight_source hM t hs ht hb
  · simp only [comp_row, show ¬2 < 1 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false]
    rw [twoRight_two hM t hs ht hb, twoMiddle_two hM t hs ht hb, twoLeft_two hM t hs ht hb]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl

end TwoCell
end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table OmegaCategory
open CylinderTables
variable {M : DirectedComplex.{u}}

def TwoLiftable (t : Table M.cylinder) : Prop :=
  ∃ x : (tensorFunctor.obj M.nu).Cell,
    (tensorFunctor.obj M.nu).source 2 x = x ∧ (chainComparison M).map x = t

lemma TwoLiftable.endpoint (a : Bool) (t : Table M) (ht : truncate 2 false t = t) :
    TwoLiftable ((M.cylinderEndpoint a).table t) := by
  refine ⟨((tensorEndpoint a).app M.nu).map t, ?_, chainComparison_endpoint_apply a t⟩
  erw [← ((tensorEndpoint a).app M.nu).map_source]
  exact congrArg ((tensorEndpoint a).app M.nu).map ht

lemma TwoLiftable.vertical (t : Table M) (ht : truncate 1 false t = t) :
    TwoLiftable (verticalTable t) := by
  refine ⟨(generatorCylinder (X := M.nu) 1 ⟨t,ht⟩).map (verticalTable (GlobeComplex.topTable 1)), ?_, ?_⟩
  · exact ((generatorCylinder (X := M.nu) 1 ⟨t,ht⟩).map_source 2 _).symm.trans
      (congrArg (generatorCylinder (X := M.nu) 1 ⟨t,ht⟩).map
        (vertical_fixed _ (GlobeComplex.topTable_bounded 1)))
  · change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨1,⟨t,ht⟩,_⟩) = _
    erw [chainComparison_generator,tableCylinder_vertical,ht]

lemma TwoLiftable.comp {a b : Table M.cylinder} (ha : TwoLiftable a) (hb : TwoLiftable b)
    (k : ℕ) (hk : k ≤ 1) (h : truncate k true a = truncate k false b) :
    TwoLiftable (DirectedComplex.Table.comp k a b h) := by
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  have hm : (tensorFunctor.obj M.nu).target k x = (tensorFunctor.obj M.nu).source k y := by
    apply chainComparison_edges_injective
    · exact (tensorFunctor.obj M.nu).source_fixed_upwards hk
        ((tensorFunctor.obj M.nu).source_target_self k x)
    · exact (tensorFunctor.obj M.nu).source_fixed_upwards hk
        ((tensorFunctor.obj M.nu).source_source_self k y)
    · rw [(chainComparison M).map_target, (chainComparison M).map_source]
      exact h
  refine ⟨(tensorFunctor.obj M.nu).comp k x y hm, ?_, ?_⟩
  · rw [← (tensorFunctor.obj M.nu).join_eq k x y hm]
    exact composite_bounded _ (by omega : k < 2) x y hx hy hm
  · exact (chainComparison M).map_comp k x y hm h

lemma TwoLiftable.join {a b : Table M.cylinder} (ha : TwoLiftable a) (hb : TwoLiftable b)
    (k : ℕ) (hk : k ≤ 1) (h : truncate k true a = truncate k false b) :
    TwoLiftable (M.cylinder.nu.join k a b) := by
  rw [M.cylinder.nu.join_eq k a b h]
  exact ha.comp hb k hk h

lemma TwoLiftable.sandwich (l c r : Table M)
    (hl : l.row 0 true = c.row 0 false) (hr : r.row 0 false = c.row 0 true)
    (hdl : truncate 2 false l = l) (hdc : truncate 1 false c = c) (hdr : truncate 2 false r = r) :
    TwoLiftable (tableSandwich l c r) :=
  ((TwoLiftable.endpoint false l hdl).join (TwoLiftable.vertical c hdc) 0 (by omega)
    (tableSandwich_match_left l c hl)).join (TwoLiftable.endpoint true r hdr) 0 (by omega)
    (tableSandwich_match_right l c r hl hr)

theorem chainComparison_crossing_twocells_surjective (hM : PositiveAcyclic M)
    (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate 2 false t = t) : TwoLiftable t := by
  have hr : TwoLiftable (twoRight t hs ht) :=
    TwoLiftable.sandwich _ _ _ (twoRight_matches hM t hs ht).1 (twoRight_matches hM t hs ht).2
      (profileEdge_bounded_two hM t hs ht hb false false)
      (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false]) (rightProfile_bounded t hs ht hb)
  have hc : TwoLiftable (twoMiddle t hs ht) :=
    TwoLiftable.sandwich _ _ _ (twoMiddle_matches hM t hs ht).1 (twoMiddle_matches hM t hs ht).2
      (profileEdge_bounded_two hM t hs ht hb false false) (crossingProfile_bounded t hs ht hb)
      (profileEdge_bounded_two hM t hs ht hb true true)
  have hl : TwoLiftable (twoLeft t hs ht) :=
    TwoLiftable.sandwich _ _ _ (twoLeft_matches hM t hs ht).1 (twoLeft_matches hM t hs ht).2
      (leftProfile_bounded t hs ht hb) (by simp only [truncate_truncate, Nat.not_lt_zero, ite_false])
      (profileEdge_bounded_two hM t hs ht hb true true)
  rw [← crossing_two_factor hM t hs ht hb]
  exact (hr.comp hc 1 le_rfl (twoRightMiddle_match hM t hs ht hb)).comp hl 1 le_rfl
    (twoRightMiddleLeft_match hM t hs ht hb)

theorem chainComparison_twocells_surjective (hM : PositiveAcyclic M) :
    Function.Surjective ((chainComparison M).onCells 2) := by
  intro t
  have hl : TwoLiftable t.val := by
    rcases endpoint_or_crossing hM t.val with ⟨a,ha⟩ | ⟨hs,ht⟩
    · rw [ha]
      apply TwoLiftable.endpoint
      change truncate 2 false (M.cylinderProjection.table t.val) = _
      erw [← Hom.table_truncate, show truncate 2 false t.val = t.val from t.property]
      rfl
    · exact chainComparison_crossing_twocells_surjective hM t.val hs ht t.property
  obtain ⟨x,hx,he⟩ := hl
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

theorem chainComparison_poset_twocells_surjective (P : Type u) [PartialOrder P] :
    Function.Surjective ((chainComparison (NormalizedChains.complex P)).onCells 2) :=
  chainComparison_twocells_surjective (NormalizedChains.complexPositiveAcyclic P)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

def verticalCell (n : ℕ) (x : X.Cells n) : (tensorFunctor.obj X).Cell :=
  (generatorCylinder n x).map (verticalTable (topTable n))

lemma verticalCell_bounded (n : ℕ) (x : X.Cells n) :
    (tensorFunctor.obj X).source (n+1) (verticalCell n x) = verticalCell n x := by
  unfold verticalCell
  erw [← (generatorCylinder n x).map_source]
  change (generatorCylinder n x).map (truncate (n+1) false (verticalTable (topTable n))) = _
  rw [vertical_fixed _ (topTable_bounded n)]

lemma verticalCell_natural (F : X ⟶ Y) (n : ℕ) (x : X.Cells n) :
    (tensorFunctor.map F).map (verticalCell n x) = verticalCell n (F.onCells n x) :=
  tensorFunctor_map_generator F n x (verticalTable (topTable n))

lemma chainComparison_verticalCell (n : ℕ) (x : M.nu.Cells n) :
    (chainComparison M).map (verticalCell n x) = verticalTable x.val := by
  change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨n,x,_⟩) = _
  erw [chainComparison_generator,tableCylinder_vertical]
  exact congrArg verticalTable x.property

lemma verticalCell_zero (x : X.Objects) : verticalCell 0 x = verticalObject x := rfl

lemma vertical_one_face (a : Bool) :
    truncate 1 a (verticalTable (topTable.{u} 1)) =
      if a then (K.{u} 1).nu.join 0 (atEnd false (topTable 1)) (verticalTable (vertex 0 true))
      else (K.{u} 1).nu.join 0 (verticalTable (vertex 0 false)) (atEnd true (topTable 1)) := by
  rw [← suspendTable_top 0, ← up_vertical, ← up_truncate]
  rw [CylinderTables.vertical_object_face _ (topTable_bounded 0)]
  cases a
  · change up (atEnd false (topTable 0)) = _
    rw [up_endpoint_false]
    exact ((K 1).nu.join_eq 0 _ _ (up_endpoint_left_matching (topTable 0))).symm
  · change up (atEnd true (topTable 0)) = _
    rw [up_endpoint_true]
    exact ((K 1).nu.join_eq 0 _ _ (up_endpoint_right_matching (topTable 0))).symm

lemma tensorUnitCell_face (k : ℕ) (a : Bool) (x : X.Cell) :
    tensorUnitCell (X.face k a x) = face k a (tensorUnitCell x) := by
  cases a
  · exact tensorUnitCell_source k x
  · exact tensorUnitCell_target k x

lemma generatorCylinder_vertical_face (n m : ℕ) (x : X.Cells n) (a : Bool) :
    (generatorCylinder n x).map (verticalTable (truncate m a (topTable n))) =
      verticalCell m ⟨X.face m a x.val, by
        cases a
        · exact X.source_source_self m x.val
        · exact X.source_target_self m x.val⟩ := by
  let v : X.Cells m := ⟨X.face m a x.val, by
    cases a
    · exact X.source_source_self m x.val
    · exact X.source_target_self m x.val⟩
  have he := tensorUnitCell_face m a x.val
  rw [tensorUnitCell_of_bounded n x, face_ofMap] at he
  change tensorUnitCell v.val = _ at he
  rw [tensorUnitCell_of_bounded m v] at he
  have h := congrArg (fun t => (eval m t).map (verticalTable (topTable m))) he
  rw [eval_ofMap_self, eval_ofMap_self] at h
  change verticalCell m v =
    (generatorCylinder n x).map ((faceMap n m a).cylinder.nu.map (verticalTable (topTable m))) at h
  rw [verticalTable_natural,faceMap_top] at h
  exact h.symm

lemma verticalCell_dimension_independent (n m : ℕ) (hnm : n ≤ m) (x : X.Cells n) :
    verticalCell m ⟨x.val, X.source_fixed_upwards hnm x.property⟩ = verticalCell n x := by
  have h := generatorCylinder_vertical_face n m x false
  have hd : truncate m false (topTable.{u} n) = topTable n :=
    (complex n).nu.source_fixed_upwards hnm (topTable_bounded n)
  rw [hd] at h
  have hx : X.face m false x.val = x.val := X.source_fixed_upwards hnm x.property
  exact (congrArg (verticalCell m) (Subtype.ext hx.symm)).trans h.symm

lemma generatorCylinder_vertical_vertex (n : ℕ) (x : X.Cells (n+1)) (a : Bool) :
    (generatorCylinder (n+1) x).map (verticalTable (vertex n a)) =
      verticalObject ⟨X.face 0 a x.val, by cases a; exact X.source_source_self 0 x.val; exact X.source_target_self 0 x.val⟩ := by
  let v : X.Objects := ⟨X.face 0 a x.val, by cases a; exact X.source_source_self 0 x.val; exact X.source_target_self 0 x.val⟩
  have he := tensorUnitCell_face 0 a x.val
  rw [tensorUnitCell_of_bounded (n+1) x, face_ofMap] at he
  change tensorUnitCell v.val = _ at he
  rw [tensorUnitCell_of_bounded 0 v] at he
  have h := congrArg (fun t => (eval 0 t).map (verticalTable (topTable 0))) he
  rw [eval_ofMap_self, eval_ofMap_self, restrictCylinder_zero_vertical] at h
  exact h.symm

lemma verticalCell_one_face (x : X.Cells 1) (a : Bool) :
    (tensorFunctor.obj X).face 1 a (verticalCell 1 x) =
      if a then (tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map x.val)
        (verticalObject ⟨X.target 0 x.val, X.source_target_self 0 x.val⟩)
      else (tensorFunctor.obj X).join 0
        (verticalObject ⟨X.source 0 x.val, X.source_source_self 0 x.val⟩)
        (((tensorEndpoint true).app X).map x.val) := by
  unfold verticalCell
  erw [← (generatorCylinder 1 x).map_face]
  have hh : (K.{u} 1).nu.face 1 a (verticalTable (topTable 1)) =
      truncate 1 a (verticalTable (topTable 1)) := by cases a <;> rfl
  rw [hh,vertical_one_face]
  cases a
  · simp only [Bool.false_eq_true, ite_false]
    erw [(generatorCylinder 1 x).map_join 0 _ _ (by
        change truncate 0 true (verticalTable (vertex 0 false)) = truncate 0 false (atEnd true (topTable 1))
        rw [← suspendTable_top 0]
        exact up_endpoint_left_matching (topTable 0)),
      generatorCylinder_endpoint,lift_top,generatorCylinder_vertical_vertex]
    rfl
  · simp only [ite_true]
    erw [(generatorCylinder 1 x).map_join 0 _ _ (by
        change truncate 0 true (atEnd false (topTable 1)) = truncate 0 false (verticalTable (vertex 0 true))
        rw [← suspendTable_top 0]
        exact up_endpoint_right_matching (topTable 0)),
      generatorCylinder_endpoint,lift_top,generatorCylinder_vertical_vertex]
    rfl

lemma generatorCylinder_matching {n k : ℕ} (x y : X.Cells n)
    (h : X.target k x.val = X.source k y.val) :
    FaceMatching k (generatorCylinder n x) (generatorCylinder n y) := by
  apply face_matching
  rw [← tensorUnitCell_of_bounded n x, ← tensorUnitCell_of_bounded n y,
    ← tensorUnitCell_face k true, ← tensorUnitCell_face k false]
  exact congrArg tensorUnitCell h

lemma generatorCylinder_comp {n k : ℕ} (hk : k < n) (x y : X.Cells n)
    (h : X.target k x.val = X.source k y.val) :
    generatorCylinder n (X.gradedComp hk x y h) =
      pasteCylinder hk (generatorCylinder n x) (generatorCylinder n y)
        (generatorCylinder_matching x y h) := by
  apply ofMap_injective
  rw [← tensorUnitCell_of_bounded n (X.gradedComp hk x y h)]
  have h' : face k true (tensorUnitCell x.val) = face k false (tensorUnitCell y.val) := by
    rw [← tensorUnitCell_face k true, ← tensorUnitCell_face k false]
    exact congrArg tensorUnitCell h
  change tensorUnitCell (X.comp k x.val y.val h) = _
  rw [tensorUnitCell_comp k x.val y.val h h']
  change comp k (tensorUnitCell x.val) (tensorUnitCell y.val) h' = _
  simp only [tensorUnitCell_of_bounded n x,tensorUnitCell_of_bounded n y]
  exact comp_ofMap hk _ _ _

lemma verticalCell_one_comp (x y : X.Cells 1) (h : X.target 0 x.val = X.source 0 y.val) :
    verticalCell 1 (X.gradedComp (by omega : 0 < 1) x y h) =
      (tensorFunctor.obj X).join 1
        ((tensorFunctor.obj X).join 0 (verticalCell 1 x) (((tensorEndpoint true).app X).map y.val))
        ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map x.val) (verticalCell 1 y)) := by
  unfold verticalCell
  rw [generatorCylinder_comp, ← suspendTable_top 0, ← up_vertical, pasteCylinder_zero_up,
    concatInterval_zero_vertical]
  rw [hom_join_val _ _ _ (zero_interval_seam _ _
    ((rectangleDiagramOfFunctor (generatorCylinder 1 x)).horizontalDiagonal_matching
      (rectangleDiagramOfFunctor (generatorCylinder 1 y))
      (zeroFaceMatching_seam (generatorCylinder_matching x y h))))]
  erw [RectangleDiagram.horizontalDiagonalOne_map,RectangleDiagram.horizontalDiagonalTwo_map,
    project_zero_vertical,suspendTable_top]
  change (tensorFunctor.obj X).join 1
    ((tensorFunctor.obj X).join 0 ((generatorCylinder 1 x).map (up (verticalTable (topTable 0))))
      ((generatorCylinder 1 y).map (atEnd true (topTable 1))))
    ((tensorFunctor.obj X).join 0 ((generatorCylinder 1 x).map (atEnd false (topTable 1)))
      ((generatorCylinder 1 y).map (up (verticalTable (topTable 0))))) = _
  rw [up_vertical,suspendTable_top,generatorCylinder_endpoint,generatorCylinder_endpoint,lift_top,lift_top]
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

lemma tensor_cells_induction (P : (tensorFunctor.obj X).Cell → Prop)
    (hend : ∀ a x, P (((tensorEndpoint a).app X).map x))
    (hvertical : ∀ n (x : X.Cells n), P (verticalCell n x))
    (hsource : ∀ k x, P x → P ((tensorFunctor.obj X).source k x))
    (htarget : ∀ k x, P x → P ((tensorFunctor.obj X).target k x))
    (hcomp : ∀ k x y (h : (tensorFunctor.obj X).target k x =
      (tensorFunctor.obj X).source k y), P x → P y →
      P ((tensorFunctor.obj X).comp k x y h)) : ∀ z, P z := by
  apply (tensorPresentation X).cells_induction P
  · rintro ⟨n,x,z⟩
    change P ((generatorCylinder n x).map z)
    apply GrayRecursive.generated n (fun t => P ((generatorCylinder n x).map t))
    · intro a t
      rw [generatorCylinder_endpoint]
      exact hend a _
    · intro t
      obtain ⟨p,a,_,he⟩ := table_classification t
      rw [he,generatorCylinder_vertical_face]
      exact hvertical p _
    · intro k s t h hs ht
      erw [(generatorCylinder n x).map_comp k s t h ((generatorCylinder n x).map_composable h)]
      exact hcomp k _ _ _ hs ht
  · exact hsource
  · exact htarget
  · exact hcomp

lemma tensor_functor_ext {F G : tensorFunctor.obj X ⟶ Y}
    (hend : ∀ a x, F.map (((tensorEndpoint a).app X).map x) =
      G.map (((tensorEndpoint a).app X).map x))
    (hvertical : ∀ n (x : X.Cells n), F.map (verticalCell n x) = G.map (verticalCell n x)) :
    F = G := by
  apply OmegaCategory.Functor.ext
  funext z
  apply tensor_cells_induction (fun t => F.map t = G.map t) hend hvertical
  · intro k x h
    rw [F.map_source,G.map_source,h]
  · intro k x h
    rw [F.map_target,G.map_target,h]
  · intro k x y h hx hy
    rw [F.map_comp k x y h (F.map_composable h), G.map_comp k x y h (G.map_composable h)]
    congr 1

lemma verticalCell_eq_of_value {n m : ℕ} (x : X.Cells n) (y : X.Cells m)
    (h : x.val = y.val) : verticalCell n x = verticalCell m y := by
  let xn : X.Cells (max n m) := ⟨x.val,X.source_fixed_upwards (le_max_left _ _) x.property⟩
  let ym : X.Cells (max n m) := ⟨y.val,X.source_fixed_upwards (le_max_right _ _) y.property⟩
  calc
    verticalCell n x = verticalCell (max n m) xn :=
      (verticalCell_dimension_independent n (max n m) (le_max_left _ _) x).symm
    _ = verticalCell (max n m) ym := congrArg (verticalCell (max n m)) (Subtype.ext h)
    _ = verticalCell m y := verticalCell_dimension_independent m (max n m) (le_max_right _ _) y

lemma verticalCell_bounded_of_bounded (p n : ℕ) (x : X.Cells p)
    (hx : X.source n x.val = x.val) :
    (tensorFunctor.obj X).source (n+1) (verticalCell p x) = verticalCell p x := by
  rw [verticalCell_eq_of_value x (⟨x.val,hx⟩ : X.Cells n) rfl]
  exact verticalCell_bounded n _

lemma tensor_truncated {n : ℕ} (hn : X.IsTruncated n) :
    (tensorFunctor.obj X).IsTruncated (n+1) := by
  apply tensor_cells_induction (fun z => (tensorFunctor.obj X).source (n+1) z = z)
  · intro a x
    rw [← ((tensorEndpoint a).app X).map_source]
    exact congrArg ((tensorEndpoint a).app X).map (X.source_fixed_upwards (by omega) (hn x))
  · intro p x
    exact verticalCell_bounded_of_bounded p n x (hn x.val)
  · intro k x hx
    by_cases hk : k < n+1
    · exact (tensorFunctor.obj X).source_fixed_upwards (by omega)
        ((tensorFunctor.obj X).source_source_self k x)
    · rw [(tensorFunctor.obj X).source_fixed_upwards (by omega : n+1 ≤ k) hx]
      exact hx
  · intro k x hx
    by_cases hk : k < n+1
    · exact (tensorFunctor.obj X).source_fixed_upwards (by omega)
        ((tensorFunctor.obj X).source_target_self k x)
    · rw [(tensorFunctor.obj X).target_eq_self_of_source_eq_self
        ((tensorFunctor.obj X).source_fixed_upwards (by omega : n+1 ≤ k) hx)]
      exact hx
  · intro k x y h hx hy
    by_cases hk : k < n+1
    · rw [(tensorFunctor.obj X).source_comp_gt (n+1) k hk x y h
        ((tensorFunctor.obj X).source_composable hk h)]
      congr 1
    · rw [(tensorFunctor.obj X).comp_of_left_source_fixed k x y h
        ((tensorFunctor.obj X).source_fixed_upwards (by omega) hx)]
      exact hy
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

lemma tensor_bounded_cells_induction (k : ℕ) (P : (tensorFunctor.obj X).Cell → Prop)
    (hend : ∀ a x, X.source k x = x → P (((tensorEndpoint a).app X).map x))
    (hvertical : ∀ r, r < k → ∀ x : X.Cells r, P (verticalCell r x))
    (hlower : ∀ r, r < k → ∀ z, (tensorFunctor.obj X).source r z = z → P z)
    (hcomp : ∀ r, r < k → ∀ x y
      (_hx : (tensorFunctor.obj X).source k x = x)
      (_hy : (tensorFunctor.obj X).source k y = y)
      (h : (tensorFunctor.obj X).target r x = (tensorFunctor.obj X).source r y),
        P x → P y → P ((tensorFunctor.obj X).comp r x y h)) :
    ∀ z, (tensorFunctor.obj X).source k z = z → P z := by
  let T := tensorFunctor.obj X
  have hg (n : ℕ) (x : X.Cells n) (t : Table (K n))
      (ht : truncate k false t = t) : P ((generatorCylinder n x).map t) := by
    have h := generated_bounded n k
      (fun t => T.source k ((generatorCylinder n x).map t) = (generatorCylinder n x).map t ∧
        P ((generatorCylinder n x).map t)) ?_ ?_ ?_ t ht
    · exact h.2
    · intro a y hy
      rw [generatorCylinder_endpoint]
      have hb : X.source k ((GlobeComplex.lift x.val x.property).map y) = (GlobeComplex.lift x.val x.property).map y := by
        erw [← (GlobeComplex.lift x.val x.property).map_source]
        exact congrArg (GlobeComplex.lift x.val x.property).map hy
      exact ⟨(((tensorEndpoint a).app X).map_source k _).symm.trans
        (congrArg ((tensorEndpoint a).app X).map hb), hend a _ hb⟩
    · intro r hr y hy
      obtain ⟨p,a,_,hpr,rfl⟩ := bounded_table_classification y hy
      rw [generatorCylinder_vertical_face]
      exact ⟨T.source_fixed_upwards (by omega : p+1 ≤ k) (verticalCell_bounded p _),
        hvertical p (by omega) _⟩
    · intro l s t h hs ht
      erw [(generatorCylinder n x).map_comp l s t h ((generatorCylinder n x).map_composable h)]
      by_cases hl : l < k
      · refine ⟨?_, hcomp l hl _ _ hs.1 ht.1 _ hs.2 ht.2⟩
        erw [T.source_comp_gt k l hl _ _ _ (T.source_composable hl
          ((generatorCylinder n x).map_composable h))]
        exact T.comp_congr_cells l _ _ hs.1 ht.1
      · erw [T.comp_of_left_source_fixed l _ _ _ (T.source_fixed_upwards (by omega) hs.1)]
        exact ht
  have hh : ∀ z : T.Cell, P (T.source k z) ∧ P (T.target k z) := by
    apply (tensorPresentation X).cells_induction
      (fun z => P (T.source k z) ∧ P (T.target k z))
    · rintro ⟨n,x,z⟩
      change Table (K n) at z
      change P (T.source k ((generatorCylinder n x).map z)) ∧
        P (T.target k ((generatorCylinder n x).map z))
      erw [← (generatorCylinder n x).map_source, ← (generatorCylinder n x).map_target]
      exact ⟨hg n x (truncate k false z) (by simp only [truncate_truncate,lt_self_iff_false,ite_false]),
        hg n x (truncate k true z) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])⟩
    · intro i z hz
      change P (T.source k (T.source i z)) ∧ P (T.target k (T.source i z))
      by_cases hi : i < k
      · erw [T.source_source, min_eq_right hi.le, T.target_source, ite_eq_right (by omega : ¬ k < i)]
        exact ⟨hlower i hi _ (T.source_source_self i z), hlower i hi _ (T.source_source_self i z)⟩
      · by_cases he : k = i
        · subst i
          erw [T.source_source_self,T.target_source_self]
          exact And.intro hz.1 hz.1
        · erw [T.source_source, min_eq_left (by omega : k ≤ i),
            T.target_source, ite_eq_left (by omega : k < i)]
          exact hz
    · intro i z hz
      change P (T.source k (T.target i z)) ∧ P (T.target k (T.target i z))
      by_cases hi : i < k
      · erw [T.source_target, ite_eq_right (by omega : ¬ k < i), T.target_target, min_eq_right hi.le]
        exact ⟨hlower i hi _ (T.source_target_self i z), hlower i hi _ (T.source_target_self i z)⟩
      · by_cases he : k = i
        · subst i
          erw [T.source_target_self,T.target_target_self]
          exact And.intro hz.2 hz.2
        · erw [T.source_target, ite_eq_left (by omega : k < i), T.target_target, min_eq_left (by omega : k ≤ i)]
          exact hz
    · intro l x y h hx hy
      by_cases hl : l < k
      · erw [T.source_comp_gt k l hl _ _ _ (T.source_composable hl h),
          T.target_comp_gt k l hl _ _ _ (T.target_composable hl h)]
        exact ⟨hcomp l hl _ _ (T.source_source_self k x) (T.source_source_self k y) _ hx.1 hy.1,
          hcomp l hl _ _ (T.source_target_self k x) (T.source_target_self k y) _ hx.2 hy.2⟩
      · erw [T.source_comp_le k l (by omega), T.target_comp_le k l (by omega)]
        exact ⟨hx.1,hy.2⟩
  intro z hz
  have hh₁ := (hh z).1
  change P ((tensorFunctor.obj X).source k z) at hh₁
  simpa only [hz] using hh₁
end Thomason.GrayRecursive.IntervalHom

end

end OAI
