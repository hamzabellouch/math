import Mathlib
import OAI.CategoryTheory.Thomason.TwoCellExchange

namespace OAI

/-! Two Cell Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma join_six_exchange (C : OmegaCategory.{u}) (k : ℕ)
    (a b c d e f u v p q r s : C.Cell)
    (hab : C.target k a = C.source k b)
    (hbc : C.target k b = C.source k c)
    (hcd : C.target k c = C.source k d)
    (hde : C.target k d = C.source k e)
    (hef : C.target k e = C.source k f)
    (huv : C.target k u = C.source k v)
    (hpq : C.target k p = C.source k q)
    (hrs : C.target k r = C.source k s)
    (h₁ : C.join k c d = C.join k u v)
    (h₂ : C.join k b u = C.join k p q)
    (h₃ : C.join k v e = C.join k r s) :
    C.join k (C.join k (C.join k a b) c) (C.join k (C.join k d e) f) =
      C.join k (C.join k (C.join k a p) (C.join k q r)) (C.join k s f) := by
  have hcu : C.source k c = C.source k u := by
    simpa only [C.join_source_le k k _ _ le_rfl hcd,
      C.join_source_le k k _ _ le_rfl huv] using congrArg (C.source k) h₁
  have hdv : C.target k d = C.target k v := by
    simpa only [C.join_target_le k k _ _ le_rfl hcd,
      C.join_target_le k k _ _ le_rfl huv] using congrArg (C.target k) h₁
  have hbu := hbc.trans hcu
  have hve := hdv.symm.trans hde
  have hbp : C.source k b = C.source k p := by
    simpa only [C.join_source_le k k _ _ le_rfl hbu,
      C.join_source_le k k _ _ le_rfl hpq] using congrArg (C.source k) h₂
  have huq : C.target k u = C.target k q := by
    simpa only [C.join_target_le k k _ _ le_rfl hbu,
      C.join_target_le k k _ _ le_rfl hpq] using congrArg (C.target k) h₂
  have hvr : C.source k v = C.source k r := by
    simpa only [C.join_source_le k k _ _ le_rfl hve,
      C.join_source_le k k _ _ le_rfl hrs] using congrArg (C.source k) h₃
  have hes : C.target k e = C.target k s := by
    simpa only [C.join_target_le k k _ _ le_rfl hve,
      C.join_target_le k k _ _ le_rfl hrs] using congrArg (C.target k) h₃
  have hap := hab.trans hbp
  have hqr := huq.symm.trans (huv.trans hvr)
  have hsf := hes.symm.trans hef
  have habc : C.target k (C.join k a b) = C.source k c := by
    rw [C.join_target_le k k _ _ le_rfl hab]; exact hbc
  have habu : C.target k (C.join k a b) = C.source k u := by
    rw [C.join_target_le k k _ _ le_rfl hab]; exact hbu
  have hdef : C.target k d = C.source k (C.join k e f) := by
    rw [C.join_source_le k k _ _ le_rfl hef]; exact hde
  have hvef : C.target k v = C.source k (C.join k e f) := by
    rw [C.join_source_le k k _ _ le_rfl hef]; exact hve
  have hpqr : C.target k p = C.source k (C.join k q r) := by
    rw [C.join_source_le k k _ _ le_rfl hqr]; exact hpq
  have hrsf : C.target k r = C.source k (C.join k s f) := by
    rw [C.join_source_le k k _ _ le_rfl hsf]; exact hrs
  have hqrs : C.target k (C.join k q r) = C.source k s := by
    rw [C.join_target_le k k _ _ le_rfl hqr]; exact hrs
  rw [C.join_assoc k d e f hde hef,
    C.join_four_middle k (C.join k a b) c d (C.join k e f) u v
      habc hcd hdef habu huv hvef h₁,
    C.join_assoc k a b u hab hbu,
    ← C.join_assoc k v e f hve hef, h₂, h₃,
    ← C.join_assoc k a p q hap hpq]
  
  rw [C.join_assoc k r s f hrs hsf]
  have hqrsf : C.target k q = C.source k (C.join k r (C.join k s f)) := by
    rw [C.join_source_le k k _ _ le_rfl hrsf]; exact hqr
  rw [C.join_assoc k (C.join k a p) q (C.join k r (C.join k s f))
      (by rw [C.join_target_le k k _ _ le_rfl hap]; exact hpq) hqrsf,
    ← C.join_assoc k q r (C.join k s f) hqr hrsf,
    ← C.join_assoc k (C.join k a p) (C.join k q r) (C.join k s f)
      (by rw [C.join_target_le k k _ _ le_rfl hap]; exact hpqr)
      (by rw [C.join_target_le k k _ _ le_rfl hqr,
        C.join_source_le k k _ _ le_rfl hsf]; exact hrs)]

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}
namespace CrossingSquare

variable (D E : CrossingSquare X)
variable (hl : X.target 1 D.left₂.val = E.left.val)
variable (hc : D.exit.val = E.entry.val)
variable (hr : D.right.val = X.source 1 E.right₂.val)

include hc in
lemma comp_left_match : X.target 0 D.left₂.val = X.source 0 E.cross.val :=
  D.left₂_target_zero.trans hc

include hc in
lemma comp_right_match : X.target 0 D.cross.val = X.source 0 E.right₂.val :=
  hc.trans E.right₂_source_zero.symm

include hl hc in
lemma comp_left₂_match :
    X.target 1 (X.join 0 D.left₂.val E.cross.val) = X.source 1 E.left₂.val := by
  rw [X.join_target_gt 1 0 _ _ (by omega) (D.comp_left_match E hc),
    hl, X.target_eq_self_of_source_eq_self E.cross.property, E.left_source]

include hc hr in
lemma comp_right₂_match :
    X.target 1 D.right₂.val = X.source 1 (X.join 0 D.cross.val E.right₂.val) := by
  rw [X.join_source_gt 1 0 _ _ (by omega) (D.comp_right_match E hc),
    D.cross.property, D.right_target, hr]

include hc in
lemma comp_lc : X.target 0 D.left.val = X.source 0 (X.join 0 D.cross.val E.cross.val) := by
  rw [X.join_source_le 0 0 _ _ le_rfl hc]; exact D.lc

include hc in
lemma comp_cr : X.target 0 (X.join 0 D.cross.val E.cross.val) = X.source 0 E.right.val := by
  rw [X.join_target_le 0 0 _ _ le_rfl hc]; exact E.cr

def comp : CrossingSquare X where
  left := D.left
  cross := ⟨X.join 0 D.cross.val E.cross.val,
    composite_bounded X (by omega : 0 < 1) _ _ D.cross.property E.cross.property hc⟩
  right := E.right
  left₂ := ⟨X.join 1 (X.join 0 D.left₂.val E.cross.val) E.left₂.val,
    composite_bounded X (by omega : 1 < 2) _ _
      (composite_bounded X (by omega : 0 < 2) _ _ D.left₂.property
        (X.source_fixed_upwards (by omega : 1 ≤ 2) E.cross.property) (D.comp_left_match E hc))
      E.left₂.property (D.comp_left₂_match E hl hc)⟩
  right₂ := ⟨X.join 1 D.right₂.val (X.join 0 D.cross.val E.right₂.val),
    composite_bounded X (by omega : 1 < 2) _ _ D.right₂.property
      (composite_bounded X (by omega : 0 < 2) _ _
        (X.source_fixed_upwards (by omega : 1 ≤ 2) D.cross.property) E.right₂.property
          (D.comp_right_match E hc))
      (D.comp_right₂_match E hc hr)⟩
  lc := D.comp_lc E hc
  cr := D.comp_cr E hc
  left_source := by
    rw [X.join_source_le 1 1 _ _ le_rfl (D.comp_left₂_match E hl hc),
      X.join_source_gt 1 0 _ _ (by omega) (D.comp_left_match E hc),
      D.left_source, E.cross.property, X.join_assoc 0 _ _ _ D.lc hc]
  right_target := by
    rw [X.join_target_le 1 1 _ _ le_rfl (D.comp_right₂_match E hc hr),
      X.join_target_gt 1 0 _ _ (by omega) (D.comp_right_match E hc),
      X.target_eq_self_of_source_eq_self D.cross.property, E.right_target,
      X.join_assoc 0 _ _ _ hc E.cr]

lemma comp_entry : (D.comp E hl hc hr).entry = D.entry := by
  apply Subtype.ext
  exact X.join_source_le 0 0 _ _ le_rfl hc

lemma comp_exit : (D.comp E hl hc hr).exit = E.exit := by
  apply Subtype.ext
  exact X.join_target_le 0 0 _ _ le_rfl hc

lemma comp_value : (D.comp E hl hc hr).value =
    (tensorFunctor.obj X).join 1 D.value E.value := by
  let T := tensorFunctor.obj X
  let G := D.comp E hl hc hr
  let lc : X.Cells 1 := ⟨X.join 0 D.left.val D.cross.val,
    composite_bounded X (by omega : 0 < 1) _ _ D.left.property D.cross.property D.lc⟩
  let cr : X.Cells 1 := ⟨X.join 0 E.cross.val E.right.val,
    composite_bounded X (by omega : 0 < 1) _ _ E.cross.property E.right.property E.cr⟩
  let U := crossingEdge lc.val D.exit E.right₂.val
  let V := crossingEdge D.left₂.val D.exit cr.val
  let P := crossingEdge D.left.val D.entry (X.join 0 D.cross.val E.right₂.val)
  let Q := whiskeredVertical D.left.val D.cross cr.val
  let R := whiskeredVertical lc.val E.cross E.right.val
  let S := crossingEdge (X.join 0 D.left₂.val E.cross.val) E.exit E.right.val
  have hh : D.exit = E.entry := Subtype.ext hc
  have hlc : X.target 0 lc.val = D.exit.val :=
    X.join_target_le 0 0 _ _ le_rfl D.lc
  have hcr : X.source 0 cr.val = E.entry.val :=
    X.join_source_le 0 0 _ _ le_rfl E.cr
  have hDcr : X.target 0 D.cross.val = X.source 0 cr.val := hc.trans hcr.symm
  have hLcE : X.target 0 lc.val = X.source 0 E.cross.val := hlc.trans hc
  have hER : X.source 0 E.right₂.val = D.exit.val := E.right₂_source_zero.trans hc.symm
  have huv : T.target 1 U = T.source 1 V := by
    change T.target 1 (crossingEdge lc.val D.exit E.right₂.val) =
      T.source 1 (crossingEdge D.left₂.val D.exit cr.val)
    rw [crossingEdge_target_one _ _ _ hlc hER,
      crossingEdge_source_one _ _ _ D.left₂_target_zero (hcr.trans hc.symm),
      X.target_eq_self_of_source_eq_self lc.property,cr.property,D.left_source,E.right_target]
  have hpq : T.target 1 P = T.source 1 Q := by
    change T.target 1 (crossingEdge D.left.val D.entry (X.join 0 D.cross.val E.right₂.val)) =
      T.source 1 (whiskeredVertical D.left.val D.cross cr.val)
    rw [crossingEdge_target_one _ _ _ D.lc
        (X.join_source_le 0 0 _ _ le_rfl (D.comp_right_match E hc)),
      X.target_eq_self_of_source_eq_self D.left.property,
      X.join_target_gt 1 0 _ _ (by omega) (D.comp_right_match E hc),
      X.target_eq_self_of_source_eq_self D.cross.property, E.right_target,
      whiskeredVertical_source D.left D.cross cr D.lc hDcr]
  have hrs : T.target 1 R = T.source 1 S := by
    change T.target 1 (whiskeredVertical lc.val E.cross E.right.val) =
      T.source 1 (crossingEdge (X.join 0 D.left₂.val E.cross.val) E.exit E.right.val)
    rw [whiskeredVertical_target lc E.cross E.right hLcE E.cr,
      crossingEdge_source_one _ _ _
        (X.join_target_le 0 0 _ _ le_rfl (D.comp_left_match E hc)) E.cr.symm,
      X.join_source_gt 1 0 _ _ (by omega) (D.comp_left_match E hc),
      E.cross.property,E.right.property,D.left_source]
  have hde : T.target 1 D.last = T.source 1 E.first := by
    rw [D.last_target,E.first_source,hl,hr,hh]
  have h₁ : T.join 1 D.last E.first = T.join 1 U V := by
    have H := crossingEdge_middle D.left₂.val E.right₂.val D.exit D.left₂_target_zero hER
    rw [D.left_source,hl,E.right_target] at H
    change T.join 1 (crossingEdge D.left₂.val D.exit D.right.val)
      (crossingEdge E.left.val E.entry E.right₂.val) = _
    rw [hr,← hh]
    exact H
  have h₂ : T.join 1 D.middle U = T.join 1 P Q := by
    change T.join 1 (whiskeredVertical D.left.val D.cross D.right.val)
      (crossingEdge (X.join 0 D.left.val D.cross.val) D.exit E.right₂.val) = _
    rw [hr]
    have H := whiskeredVertical_exchange_right D.left D.cross E.right₂.val D.lc
      (D.comp_right_match E hc)
    rw [E.right_target] at H
    exact H
  have h₃ : T.join 1 V E.middle = T.join 1 R S := by
    have H := whiskeredVertical_exchange_left D.left₂.val E.cross E.right
      (D.comp_left_match E hc) E.cr
    rw [hl,D.left_source] at H
    change T.join 1 (crossingEdge D.left₂.val D.exit cr.val)
      (whiskeredVertical E.left.val E.cross E.right.val) = _
    rw [hh]
    exact H
  have hfirst : G.first = T.join 1 D.first P := by
    change crossingEdge D.left.val G.entry
      (X.join 1 D.right₂.val (X.join 0 D.cross.val E.right₂.val)) = _
    rw [D.comp_entry E hl hc hr]
    exact crossingEdge_comp_right D.left D.entry D.right₂.val (X.join 0 D.cross.val E.right₂.val)
      D.lc D.right₂_source_zero
      (X.join_source_le 0 0 _ _ le_rfl (D.comp_right_match E hc))
      (D.comp_right₂_match E hc hr)
  have hmiddle : G.middle = T.join 1 Q R := by
    have he : G.cross = X.gradedComp (by omega : 0 < 1) D.cross E.cross hc := by
      apply Subtype.ext
      exact X.join_eq 0 D.cross.val E.cross.val hc
    change whiskeredVertical D.left.val G.cross E.right.val = _
    rw [he]
    exact whiskeredVertical_comp D.left D.cross E.cross E.right D.lc hc E.cr
  have hlast : G.last = T.join 1 S E.last := by
    change crossingEdge (X.join 1 (X.join 0 D.left₂.val E.cross.val) E.left₂.val)
      G.exit E.right.val = _
    rw [D.comp_exit E hl hc hr]
    exact crossingEdge_comp_left (X.join 0 D.left₂.val E.cross.val) E.left₂.val E.exit E.right
      (X.join_target_le 0 0 _ _ le_rfl (D.comp_left_match E hc)) E.left₂_target_zero E.cr.symm
      (D.comp_left₂_match E hl hc)
  have H := T.join_six_exchange 1 D.first D.middle D.last E.first E.middle E.last U V P Q R S
    D.first_middle D.middle_last hde E.first_middle E.middle_last huv hpq hrs h₁ h₂ h₃
  change T.join 1 (T.join 1 G.first G.middle) G.last =
    T.join 1 (T.join 1 (T.join 1 D.first D.middle) D.last)
      (T.join 1 (T.join 1 E.first E.middle) E.last)
  rw [hfirst,hmiddle,hlast]
  exact H.symm

lemma seam_of_matching {M : DirectedComplex.{u}} (D E : CrossingSquare M.nu)
    (h : (tensorFunctor.obj M.nu).target 1 D.value =
      (tensorFunctor.obj M.nu).source 1 E.value) :
    M.nu.target 1 D.left₂.val = E.left.val ∧
      D.exit.val = E.entry.val ∧ D.right.val = M.nu.source 1 E.right₂.val := by
  rw [D.target_one,E.source_one] at h
  obtain ⟨h₁,h₂,h₃⟩ := chainComparison_crossingEdge_injective
      (M.nu.target 1 D.left₂.val) E.left.val D.exit E.entry
      D.right.val (M.nu.source 1 E.right₂.val)
      (by change M.nu.target 0 (M.nu.target 1 D.left₂.val) = _
          rw [M.nu.target_target,min_eq_left (by omega : 0 ≤ 1)]; exact D.left₂_target_zero)
      D.cr.symm E.lc
      (by change M.nu.source 0 (M.nu.source 1 E.right₂.val) = _
          rw [M.nu.source_source,min_eq_left (by omega : 0 ≤ 1)]; exact E.right₂_source_zero)
      (congrArg (chainComparison M).map h)
  exact ⟨h₁,congrArg Subtype.val h₂,h₃⟩

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma join_comp_source (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (hbc : C.target l b = C.source l c)
    (hab : C.target k a = C.source k b) :
    C.join k a (C.join l b c) =
      C.join l (C.join k (C.source l a) b) (C.join k a c) := by
  have hac : C.target k a = C.source k c := by
    have hh := congrArg (C.source k) hbc
    rw [C.source_target, ite_eq_left hkl, C.source_source, min_eq_left hkl.le] at hh
    exact hab.trans hh
  have hsab : C.target k (C.source l a) = C.source k b := by
    rw [C.target_source, ite_eq_left hkl]; exact hab
  have h := C.join_interchange k l hkl (C.source l a) a b c
    (C.target_source_self l a) hbc hsab hac
  rw [C.join_left_unit l (C.source l a) a (C.source_source_self l a)
    (C.target_source_self l a)] at h
  exact h

lemma join_comp_target (C : OmegaCategory.{u}) (k l : ℕ) (hkl : k < l)
    (a b c : C.Cell) (hbc : C.target l b = C.source l c)
    (hba : C.target k b = C.source k a) :
    C.join k (C.join l b c) a =
      C.join l (C.join k b a) (C.join k c (C.target l a)) := by
  have hca : C.target k c = C.source k a := by
    have hh := congrArg (C.target k) hbc
    rw [C.target_target, min_eq_left hkl.le, C.target_source, ite_eq_left hkl] at hh
    exact hh.symm.trans hba
  have hcat : C.target k c = C.source k (C.target l a) := by
    rw [C.source_target, ite_eq_left hkl]; exact hca
  have h := C.join_interchange k l hkl b c a (C.target l a)
    hbc (C.source_target_self l a).symm hba hcat
  rw [C.join_right_unit l a (C.target l a) (C.source_target_self l a)
    (C.source_target_self l a).symm] at h
  exact h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}

lemma crossingEdge_whisker_left (a l : X.Cell) (c : X.Objects) (r : X.Cell)
    (h : X.target 0 a = X.source 0 l) (hl : X.target 0 l = c.val)
    (hr : X.source 0 r = c.val) :
    crossingEdge (X.join 0 a l) c r = (tensorFunctor.obj X).join 0
      (((tensorEndpoint false).app X).map a) (crossingEdge l c r) := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint false).app X
  unfold crossingEdge
  erw [E.map_join 0 _ _ h]
  rw [T.join_assoc 0 _ _ _ (E.map_composable h) (crossingEdge_left_matching l c hl),
    T.join_assoc 0 _ _ _ (by
      rw [T.join_source_le 0 0 _ _ le_rfl (crossingEdge_left_matching l c hl)]
      exact E.map_composable h) (crossingEdge_right_matching l c r hl hr)]

lemma crossingEdge_whisker_right (l : X.Cell) (c : X.Objects) (r a : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val)
    (h : X.target 0 r = X.source 0 a) :
    crossingEdge l c (X.join 0 r a) = (tensorFunctor.obj X).join 0
      (crossingEdge l c r) (((tensorEndpoint true).app X).map a) := by
  unfold crossingEdge
  erw [((tensorEndpoint true).app X).map_join 0 _ _ h,
    (tensorFunctor.obj X).join_assoc 0 _ _ _ (crossingEdge_right_matching l c r hl hr)
      (((tensorEndpoint true).app X).map_composable h)]

lemma whiskeredVertical_whisker_left (a l : X.Cell) (c : X.Cells 1) (r : X.Cell)
    (h : X.target 0 a = X.source 0 l) (hl : X.target 0 l = X.source 0 c.val)
    (hr : X.target 0 c.val = X.source 0 r) :
    whiskeredVertical (X.join 0 a l) c r = (tensorFunctor.obj X).join 0
      (((tensorEndpoint false).app X).map a) (whiskeredVertical l c r) := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint false).app X
  unfold whiskeredVertical
  erw [E.map_join 0 _ _ h]
  rw [T.join_assoc 0 _ _ _ (E.map_composable h) (whiskeredVertical_left_match l c hl),
    T.join_assoc 0 _ _ _ (by
      rw [T.join_source_le 0 0 _ _ le_rfl (whiskeredVertical_left_match l c hl)]
      exact E.map_composable h) (whiskeredVertical_right_match l c r hl hr)]

lemma whiskeredVertical_whisker_right (l : X.Cell) (c : X.Cells 1) (r a : X.Cell)
    (hl : X.target 0 l = X.source 0 c.val) (hr : X.target 0 c.val = X.source 0 r)
    (h : X.target 0 r = X.source 0 a) :
    whiskeredVertical l c (X.join 0 r a) = (tensorFunctor.obj X).join 0
      (whiskeredVertical l c r) (((tensorEndpoint true).app X).map a) := by
  unfold whiskeredVertical
  erw [((tensorEndpoint true).app X).map_join 0 _ _ h,
    (tensorFunctor.obj X).join_assoc 0 _ _ _ (whiskeredVertical_right_match l c r hl hr)
      (((tensorEndpoint true).app X).map_composable h)]

namespace CrossingSquare
variable (D : CrossingSquare X)

lemma source_zero : (tensorFunctor.obj X).source 0 D.value =
    ((tensorEndpoint false).app X).map (X.source 0 D.left.val) := by
  rw [value, (tensorFunctor.obj X).join_source_le 0 1 _ _ (by omega) D.firstMiddle_last,
    (tensorFunctor.obj X).join_source_le 0 1 _ _ (by omega) D.first_middle]
  exact crossingEdge_source _ _ _ D.lc D.right₂_source_zero

lemma target_zero : (tensorFunctor.obj X).target 0 D.value =
    ((tensorEndpoint true).app X).map (X.target 0 D.right.val) := by
  rw [value, (tensorFunctor.obj X).join_target_le 0 1 _ _ (by omega) D.firstMiddle_last]
  exact crossingEdge_target _ _ _ D.left₂_target_zero D.cr.symm

variable (a : X.Cells 2) (h : X.target 0 a.val = X.source 0 D.left.val)

include h in
lemma whisker_left_match : X.target 0 a.val = X.source 0 D.left₂.val :=
  h.trans D.left₂_source_zero.symm

include h in
lemma whisker_left_source_match : X.target 0 (X.source 1 a.val) = X.source 0 D.left.val := by
  rw [X.target_source, ite_eq_left (by omega : 0 < 1)]; exact h

def whiskerLeft : CrossingSquare X where
  left := ⟨X.join 0 (X.source 1 a.val) D.left.val,
    composite_bounded X (by omega : 0 < 1) _ _ (X.source_source_self 1 a.val) D.left.property
      (D.whisker_left_source_match a h)⟩
  cross := D.cross
  right := D.right
  left₂ := ⟨X.join 0 a.val D.left₂.val,
    composite_bounded X (by omega : 0 < 2) _ _ a.property D.left₂.property
      (D.whisker_left_match a h)⟩
  right₂ := D.right₂
  lc := by
    rw [X.join_target_le 0 0 _ _ le_rfl (D.whisker_left_source_match a h)]
    exact D.lc
  cr := D.cr
  left_source := by
    rw [X.join_source_gt 1 0 _ _ (by omega) (D.whisker_left_match a h),
      D.left_source, X.join_assoc 0 _ _ _ (D.whisker_left_source_match a h) D.lc]
  right_target := D.right_target

lemma whiskerLeft_value : (D.whiskerLeft a h).value = (tensorFunctor.obj X).join 0
    (((tensorEndpoint false).app X).map a.val) D.value := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint false).app X
  let G := D.whiskerLeft a h
  have hfirst : G.first = T.join 0 (E.map (X.source 1 a.val)) D.first :=
    crossingEdge_whisker_left _ _ _ _ (D.whisker_left_source_match a h) D.lc D.right₂_source_zero
  have hmiddle : G.middle = T.join 0 (E.map (X.source 1 a.val)) D.middle :=
    whiskeredVertical_whisker_left _ _ _ _ (D.whisker_left_source_match a h) D.lc D.cr
  have hlast : G.last = T.join 0 (E.map a.val) D.last :=
    crossingEdge_whisker_left _ _ _ _ (D.whisker_left_match a h) D.left₂_target_zero D.cr.symm
  change T.join 1 (T.join 1 G.first G.middle) G.last = _
  rw [hfirst,hmiddle,hlast]
  have hm₁ : T.target 0 (E.map a.val) = T.source 0 D.first := by
    rw [endpoint_target, first, crossingEdge_source _ _ _ D.lc D.right₂_source_zero, h]
  have hm₂ : T.target 0 (E.map a.val) = T.source 0 (T.join 1 D.first D.middle) := by
    rw [T.join_source_le 0 1 _ _ (by omega) D.first_middle]; exact hm₁
  have hms : T.target 0 (T.source 1 (E.map a.val)) = T.source 0 D.first := by
    rw [T.target_source, ite_eq_left (by omega : 0 < 1)]; exact hm₁
  change _ = T.join 0 (E.map a.val) (T.join 1 (T.join 1 D.first D.middle) D.last)
  rw [T.join_comp_source 0 1 (by omega) _ _ _ D.firstMiddle_last hm₂,
    T.join_comp_source 0 1 (by omega) _ _ _ D.first_middle hms,
    T.source_source_self, endpoint_source]

variable (hr : X.target 0 D.right.val = X.source 0 a.val)

include hr in
lemma whisker_right_match : X.target 0 D.right₂.val = X.source 0 a.val :=
  D.right₂_target_zero.trans hr

include hr in
lemma whisker_right_target_match : X.target 0 D.right.val = X.source 0 (X.target 1 a.val) := by
  rw [X.source_target, ite_eq_left (by omega : 0 < 1)]; exact hr

def whiskerRight : CrossingSquare X where
  left := D.left
  cross := D.cross
  right := ⟨X.join 0 D.right.val (X.target 1 a.val),
    composite_bounded X (by omega : 0 < 1) _ _ D.right.property (X.source_target_self 1 a.val)
      (D.whisker_right_target_match a hr)⟩
  left₂ := D.left₂
  right₂ := ⟨X.join 0 D.right₂.val a.val,
    composite_bounded X (by omega : 0 < 2) _ _ D.right₂.property a.property
      (D.whisker_right_match a hr)⟩
  lc := D.lc
  cr := by
    rw [X.join_source_le 0 0 _ _ le_rfl (D.whisker_right_target_match a hr)]
    exact D.cr
  left_source := D.left_source
  right_target := by
    rw [X.join_target_gt 1 0 _ _ (by omega) (D.whisker_right_match a hr),
      D.right_target, X.join_assoc 0 _ _ _ D.cr (D.whisker_right_target_match a hr)]

lemma whiskerRight_value : (D.whiskerRight a hr).value = (tensorFunctor.obj X).join 0
    D.value (((tensorEndpoint true).app X).map a.val) := by
  let T := tensorFunctor.obj X
  let E := (tensorEndpoint true).app X
  let G := D.whiskerRight a hr
  have hfirst : G.first = T.join 0 D.first (E.map a.val) :=
    crossingEdge_whisker_right _ _ _ _ D.lc D.right₂_source_zero (D.whisker_right_match a hr)
  have hmiddle : G.middle = T.join 0 D.middle (E.map (X.target 1 a.val)) :=
    whiskeredVertical_whisker_right _ _ _ _ D.lc D.cr (D.whisker_right_target_match a hr)
  have hlast : G.last = T.join 0 D.last (E.map (X.target 1 a.val)) :=
    crossingEdge_whisker_right _ _ _ _ D.left₂_target_zero D.cr.symm
      (D.whisker_right_target_match a hr)
  change T.join 1 (T.join 1 G.first G.middle) G.last = _
  rw [hfirst,hmiddle,hlast]
  have hm₁ : T.target 0 D.first = T.source 0 (E.map a.val) := by
    rw [endpoint_source, first, crossingEdge_target _ _ _ D.lc D.right₂_source_zero,
      D.right₂_target_zero, hr]
  have hm₂ : T.target 0 (T.join 1 D.first D.middle) = T.source 0 (E.map a.val) := by
    have hmf := congrArg (T.target 0) D.first_middle
    rw [T.target_target, min_eq_left (by omega : 0 ≤ 1), T.target_source,
      ite_eq_left (by omega : 0 < 1)] at hmf
    rw [T.join_target_le 0 1 _ _ (by omega) D.first_middle]
    exact hmf.symm.trans hm₁
  change _ = T.join 0 (T.join 1 (T.join 1 D.first D.middle) D.last) (E.map a.val)
  rw [T.join_comp_target 0 1 (by omega) _ _ _ D.firstMiddle_last hm₂,
    T.join_comp_target 0 1 (by omega) _ _ _ D.first_middle hm₁, endpoint_target]

end CrossingSquare
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

namespace CrossingSquare

def map (D : CrossingSquare X) (F : X ⟶ Y) : CrossingSquare Y where
  left := F.onCells 1 D.left
  cross := F.onCells 1 D.cross
  right := F.onCells 1 D.right
  left₂ := F.onCells 2 D.left₂
  right₂ := F.onCells 2 D.right₂
  lc := by change Y.target 0 (F.map _) = Y.source 0 (F.map _)
           rw [← F.map_target, ← F.map_source, D.lc]
  cr := by change Y.target 0 (F.map _) = Y.source 0 (F.map _)
           rw [← F.map_target, ← F.map_source, D.cr]
  left_source := by
    change Y.source 1 (F.map D.left₂.val) = Y.join 0 (F.map D.left.val) (F.map D.cross.val)
    rw [← F.map_source, D.left_source, F.map_join 0 _ _ D.lc]
  right_target := by
    change Y.target 1 (F.map D.right₂.val) = Y.join 0 (F.map D.cross.val) (F.map D.right.val)
    rw [← F.map_target, D.right_target, F.map_join 0 _ _ D.cr]

lemma map_entry (D : CrossingSquare X) (F : X ⟶ Y) :
    (D.map F).entry = F.objects D.entry := by
  apply Subtype.ext
  exact (F.map_source 0 D.cross.val).symm

lemma map_exit (D : CrossingSquare X) (F : X ⟶ Y) :
    (D.map F).exit = F.objects D.exit := by
  apply Subtype.ext
  exact (F.map_target 0 D.cross.val).symm

lemma map_value (D : CrossingSquare X) (F : X ⟶ Y) :
    (D.map F).value = (tensorFunctor.map F).map D.value := by
  have hfirst : (D.map F).first = (tensorFunctor.map F).map D.first := by
    rw [first, D.map_entry, first, tensorFunctor_map_crossingEdge F _ _ _ D.lc D.right₂_source_zero]
    rfl
  have hlast : (D.map F).last = (tensorFunctor.map F).map D.last := by
    rw [last, D.map_exit, last, tensorFunctor_map_crossingEdge F _ _ _ D.left₂_target_zero D.cr.symm]
    rfl
  have hmiddle : (D.map F).middle = (tensorFunctor.map F).map D.middle := by
    rw [middle, middle,
      (tensorFunctor.map F).map_join 0 _ _ D.middle_matching_right,
      (tensorFunctor.map F).map_join 0 _ _ D.middle_matching_left,
      tensorFunctor_map_endpoint, tensorFunctor_map_endpoint,
      verticalCell_natural]
    rfl
  rw [value, value, hfirst, hmiddle, hlast,
    (tensorFunctor.map F).map_join 1 _ _ D.firstMiddle_last,
    (tensorFunctor.map F).map_join 1 _ _ D.first_middle]

end CrossingSquare

inductive SquareNormal (X : OmegaCategory.{u}) : (tensorFunctor.obj X).Cell → Prop
  | endpoint (a : Bool) (x : X.Cell) (hx : X.source 2 x = x) :
      SquareNormal X (((tensorEndpoint a).app X).map x)
  | crossing (D : CrossingSquare X) : SquareNormal X D.value

lemma SquareNormal.bounded {z : (tensorFunctor.obj X).Cell} (hz : SquareNormal X z) :
    (tensorFunctor.obj X).source 2 z = z := by
  cases hz with
  | endpoint a x hx => rw [endpoint_source,hx]
  | crossing D => exact D.bounded

lemma SquareNormal.map (F : X ⟶ Y) {z : (tensorFunctor.obj X).Cell} (hz : SquareNormal X z) :
    SquareNormal Y ((tensorFunctor.map F).map z) := by
  cases hz with
  | endpoint a x hx =>
    rw [tensorFunctor_map_endpoint]
    exact .endpoint a _ ((F.map_source 2 x).symm.trans (congrArg F.map hx))
  | crossing D => rw [← D.map_value F]; exact .crossing _

lemma globe_inv_square_normal (n : ℕ) (t : Table (K.{u} n)) (ht : truncate 2 false t = t) :
    SquareNormal (complex n).nu ((globeTensorIso n).inv.map t) := by
  rcases CylinderTables.endpoint_or_crossing (complexPositiveAcyclic n) t with ⟨a,ha⟩ | ⟨hs,he⟩
  · have hp : truncate 2 false (CylinderTables.project t) = CylinderTables.project t := by
      change truncate 2 false ((complex n).cylinderProjection.table t) = _
      rw [← Hom.table_truncate,ht]
      rfl
    have him : (chainComparison (complex n)).map (((tensorEndpoint a).app (complex n).nu).map
        (CylinderTables.project t)) = t := (chainComparison_endpoint_apply a _).trans ha.symm
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hb := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map (((tensorEndpoint a).app (complex n).nu).map (CylinderTables.project t))) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hb
    rw [hb] at hi
    rw [← hi]
    exact .endpoint a _ hp
  · let D := CrossingSquare.ofTable (complexPositiveAcyclic n) ⟨t,ht⟩ hs he
    have him : (chainComparison (complex n)).map D.value = t :=
      CrossingSquare.image_ofTable (complexPositiveAcyclic n) ⟨t,ht⟩ hs he
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hb := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map D.value) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hb
    rw [hb] at hi
    rw [← hi]
    exact .crossing D

lemma generatorCylinder_square_normal (n : ℕ) (x : X.Cells n) (t : Table (K.{u} n))
    (ht : truncate 2 false t = t) : SquareNormal X ((generatorCylinder n x).map t) := by
  rw [generatorCylinder_as_map]
  exact (globe_inv_square_normal n t ht).map _

lemma vertical_square_normal (n : ℕ) (hn : n < 2) (x : X.Cells n) :
    SquareNormal X (verticalCell n x) :=
  generatorCylinder_square_normal n x _
    ((K n).nu.source_fixed_upwards (by omega : n+1 ≤ 2)
      (vertical_fixed _ (topTable_bounded n)))

lemma SquareNormal.join_zero {x y : (tensorFunctor.obj X).Cell}
    (hx : SquareNormal X x) (hy : SquareNormal X y)
    (h : (tensorFunctor.obj X).target 0 x = (tensorFunctor.obj X).source 0 y) :
    SquareNormal X ((tensorFunctor.obj X).join 0 x y) := by
  cases hx with
  | endpoint a x hx =>
    cases hy with
    | endpoint b y hy =>
      rw [endpoint_target,endpoint_source] at h
      obtain ⟨hab,hxy⟩ := (tensorEndpoint_eq_iff a b _ _).mp h
      subst b
      rw [← ((tensorEndpoint a).app X).map_join 0 x y hxy]
      exact .endpoint a _ (composite_bounded X (by omega : 0 < 2) x y hx hy hxy)
    | crossing D =>
      rw [endpoint_target,D.source_zero] at h
      obtain ⟨ha,hxl⟩ := (tensorEndpoint_eq_iff a false _ _).mp h
      subst a
      rw [← D.whiskerLeft_value ⟨x,hx⟩ hxl]
      exact .crossing _
  | crossing D =>
    cases hy with
    | endpoint a y hy =>
      rw [D.target_zero,endpoint_source] at h
      obtain ⟨ha,hry⟩ := (tensorEndpoint_eq_iff true a _ _).mp h
      subst a
      rw [← D.whiskerRight_value ⟨y,hy⟩ hry]
      exact .crossing _
    | crossing E =>
      rw [D.target_zero,E.source_zero] at h
      exact False.elim (Bool.noConfusion ((tensorEndpoint_eq_iff true false _ _).mp h).1)

lemma EdgeNormal.square {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) :
    SquareNormal X z := by
  cases hz with
  | endpoint a x hx => exact .endpoint a x (X.source_fixed_upwards (by omega : 1 ≤ 2) hx)
  | crossing l c r hl hr hdl hdr =>
    have hv : SquareNormal X (verticalObject c) := vertical_square_normal 0 (by omega) c
    exact ((SquareNormal.endpoint false l (X.source_fixed_upwards (by omega : 1 ≤ 2) hdl)).join_zero hv
      (crossingEdge_left_matching l c hl)).join_zero
      (.endpoint true r (X.source_fixed_upwards (by omega : 1 ≤ 2) hdr))
      (crossingEdge_right_matching l c r hl hr)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}} {M : DirectedComplex.{u}}

lemma endpoint_crossing_square_not_matching (a : Bool) (x : X.Cell) (D : CrossingSquare X)
    (h : (tensorFunctor.obj X).target 1 (((tensorEndpoint a).app X).map x) =
      (tensorFunctor.obj X).source 1 D.value) : False := by
  let T := tensorFunctor.obj X
  have hs := congrArg (T.source 0) h
  have ht := congrArg (T.target 0) h
  rw [T.source_target,ite_eq_left (by omega : 0 < 1),T.source_source,min_eq_left (by omega : 0 ≤ 1)] at hs
  rw [T.target_target,min_eq_left (by omega : 0 ≤ 1),T.target_source,ite_eq_left (by omega : 0 < 1)] at ht
  change (tensorFunctor.obj X).source 0 _ = (tensorFunctor.obj X).source 0 _ at hs
  change (tensorFunctor.obj X).target 0 _ = (tensorFunctor.obj X).target 0 _ at ht
  rw [endpoint_source,D.source_zero] at hs
  rw [endpoint_target,D.target_zero] at ht
  exact Bool.noConfusion (((tensorEndpoint_eq_iff a true _ _).mp ht).1.symm.trans
    ((tensorEndpoint_eq_iff a false _ _).mp hs).1)

lemma crossing_square_endpoint_not_matching (D : CrossingSquare X) (a : Bool) (x : X.Cell)
    (h : (tensorFunctor.obj X).target 1 D.value =
      (tensorFunctor.obj X).source 1 (((tensorEndpoint a).app X).map x)) : False := by
  let T := tensorFunctor.obj X
  have hs := congrArg (T.source 0) h
  have ht := congrArg (T.target 0) h
  rw [T.source_target,ite_eq_left (by omega : 0 < 1),T.source_source,min_eq_left (by omega : 0 ≤ 1)] at hs
  rw [T.target_target,min_eq_left (by omega : 0 ≤ 1),T.target_source,ite_eq_left (by omega : 0 < 1)] at ht
  change (tensorFunctor.obj X).source 0 _ = (tensorFunctor.obj X).source 0 _ at hs
  change (tensorFunctor.obj X).target 0 _ = (tensorFunctor.obj X).target 0 _ at ht
  rw [D.source_zero,endpoint_source] at hs
  rw [D.target_zero,endpoint_target] at ht
  exact Bool.noConfusion (((tensorEndpoint_eq_iff true a _ _).mp ht).1.trans
    ((tensorEndpoint_eq_iff false a _ _).mp hs).1.symm)

lemma SquareNormal.join_one {x y : (tensorFunctor.obj M.nu).Cell}
    (hx : SquareNormal M.nu x) (hy : SquareNormal M.nu y)
    (h : (tensorFunctor.obj M.nu).target 1 x = (tensorFunctor.obj M.nu).source 1 y) :
    SquareNormal M.nu ((tensorFunctor.obj M.nu).join 1 x y) := by
  cases hx with
  | endpoint a x hx =>
    cases hy with
    | endpoint b y hy =>
      rw [endpoint_target,endpoint_source] at h
      obtain ⟨hab,hxy⟩ := (tensorEndpoint_eq_iff a b _ _).mp h
      subst b
      rw [← ((tensorEndpoint a).app M.nu).map_join 1 x y hxy]
      exact .endpoint a _ (composite_bounded M.nu (by omega : 1 < 2) x y hx hy hxy)
    | crossing D => exact False.elim (endpoint_crossing_square_not_matching a x D h)
  | crossing D =>
    cases hy with
    | endpoint a y hy => exact False.elim (crossing_square_endpoint_not_matching D a y h)
    | crossing E =>
      obtain ⟨hl,hc,hr⟩ := D.seam_of_matching E h
      rw [← D.comp_value E hl hc hr]
      exact .crossing _

lemma tensor_square_normal (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (tensorFunctor.obj M.nu).source 2 z = z) : SquareNormal M.nu z := by
  apply tensor_bounded_cells_induction 2 (SquareNormal M.nu) ?_ ?_ ?_ ?_ z hz
  · intro a x hx; exact .endpoint a x hx
  · exact vertical_square_normal
  · intro r hr t ht
    exact (tensor_edge_normal t ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega : r ≤ 1) ht)).square
  · intro r hr x y hx hy hm hnx hny
    rw [← (tensorFunctor.obj M.nu).join_eq r x y hm]
    have he : r = 0 ∨ r = 1 := by omega
    rcases he with rfl | rfl
    · exact hnx.join_zero hny hm
    · exact hnx.join_one hny hm

lemma chainComparison_twocells_injective (x y : (tensorFunctor.obj M.nu).Cell)
    (hx : (tensorFunctor.obj M.nu).source 2 x = x) (hy : (tensorFunctor.obj M.nu).source 2 y = y)
    (he : (chainComparison M).map x = (chainComparison M).map y) : x = y := by
  have hnx := tensor_square_normal x hx
  have hny := tensor_square_normal y hy
  cases hnx with
  | endpoint a x hx =>
    exact ((chainComparison_endpoint_fiber y a x).mp
      (he.symm.trans (chainComparison_endpoint_apply a x))).symm
  | crossing D =>
    cases hny with
    | endpoint a y hy =>
      exact (chainComparison_endpoint_fiber _ a y).mp (he.trans (chainComparison_endpoint_apply a y))
    | crossing E => exact congrArg CrossingSquare.value (D.image_ext E he)

theorem chainComparison_twocells_bijective (hM : PositiveAcyclic M) :
    Function.Bijective ((chainComparison M).onCells 2) := by
  refine ⟨?_, chainComparison_twocells_surjective hM⟩
  intro x y he
  apply Subtype.ext
  exact chainComparison_twocells_injective x.val y.val x.property y.property (congrArg Subtype.val he)

theorem chainComparison_poset_twocells_bijective (P : Type u) [PartialOrder P] :
    Function.Bijective ((chainComparison (NormalizedChains.complex P)).onCells 2) :=
  chainComparison_twocells_bijective (NormalizedChains.complexPositiveAcyclic P)
end Thomason.GrayRecursive.IntervalHom

end

end OAI
