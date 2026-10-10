import Mathlib
import OAI.CategoryTheory.Thomason.PastingInterchange

namespace OAI

/-! Interval Categories. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace PositiveInterchange
variable {n k l : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching (k+1) F G) (j : FaceMatching (k+1) F' G')
    (h : FaceMatching (l+1) F F') (i : FaceMatching (l+1) G G')

abbrev A := (rectangleDiagramOfFunctor F).diagonal
abbrev B := CylinderComposition.secondDiagonal F G e
abbrev C := CylinderComposition.secondDiagonal F F' h

def Z : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory (F.map (atEnd false (vertex n false))) (F.map (atEnd true (vertex n true)))) :=
  homCast (rectangleDiagramOfFunctor G').diagonal
    ((e.vertices false false).trans (i.vertices false false)).symm
    ((e.vertices true true).trans (i.vertices true true)).symm

abbrev AB : FaceMatching k (A F) (B F G e) := CylinderComposition.diagonal_matching F G e
abbrev AC : FaceMatching l (A F) (C F F' h) := CylinderComposition.diagonal_matching F F' h

lemma BZ : FaceMatching l (B F G e) (Z F G G' e i) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching G G' i) (fun _ => rfl) (fun _ => rfl)

include j in
lemma CZ : FaceMatching k (C F F' h) (Z F G G' e i) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching F' G' j) (fun _ => rfl) (fun _ => rfl)

lemma BZ_map (hl : l < n) (x : Table (K.{u} n)) :
    ((pasteCylinder hl (B F G e) (Z F G G' e i) (BZ F G G' e i)).map x).val =
      (pasteCylinder (Nat.add_lt_add_right hl 1) G G' i).map (up x) := by
  rw [pasteCylinder_succ_up hl]
  apply pasteCylinder_val_congr <;> intro w <;> rfl

include j in
lemma CZ_map (hk : k < n) (x : Table (K.{u} n)) :
    ((pasteCylinder hk (C F F' h) (Z F G G' e i) (CZ F G F' G' e j h i)).map x).val =
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j).map (up x) := by
  rw [pasteCylinder_succ_up hk]
  apply pasteCylinder_val_congr <;> intro w <;> rfl

lemma outer_e (hl : l < n)
    (ee : FaceMatching (k+1) (pasteCylinder (Nat.add_lt_add_right hl 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hl 1) G G' i)) :
    FaceMatching k (pasteCylinder hl (A F) (C F F' h) (AC F F' h))
      (pasteCylinder hl (B F G e) (Z F G G' e i) (BZ F G G' e i)) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching _ _ ee)
    (fun x => (pasteCylinder_succ_up hl F F' h x).symm) (BZ_map F G G' e i hl)

lemma outer_h (hk : k < n)
    (hh : FaceMatching (l+1) (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j)) :
    FaceMatching l (pasteCylinder hk (A F) (B F G e) (AB F G e))
      (pasteCylinder hk (C F F' h) (Z F G G' e i) (CZ F G F' G' e j h i)) :=
  FaceMatching.of_val _ _ _ _ (CylinderComposition.diagonal_matching _ _ hh)
    (fun x => (pasteCylinder_succ_up hk F G e x).symm) (CZ_map F G F' G' e j h i hk)

end PositiveInterchange

lemma pasteCylinder_interchange (n k l : ℕ) (hkl : k < l) (hl : l < n)
    {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y)
    (e : FaceMatching k F G) (j : FaceMatching k F' G')
    (h : FaceMatching l F F') (i : FaceMatching l G G')
    (ee : FaceMatching k (pasteCylinder hl F F' h) (pasteCylinder hl G G' i))
    (hh : FaceMatching l (pasteCylinder (Nat.lt_trans hkl hl) F G e)
      (pasteCylinder (Nat.lt_trans hkl hl) F' G' j)) :
    pasteCylinder (Nat.lt_trans hkl hl) (pasteCylinder hl F F' h) (pasteCylinder hl G G' i) ee =
      pasteCylinder hl (pasteCylinder (Nat.lt_trans hkl hl) F G e)
        (pasteCylinder (Nat.lt_trans hkl hl) F' G' j) hh := by
  induction k generalizing n l Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      cases l with
      | zero => omega
      | succ l => exact pasteCylinder_interchange_zero (by omega) F G F' G' e j h i ee hh
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases l with
      | zero => omega
      | succ l =>
        have hkl' : k < l := by omega
        have hl' : l < n := by omega
        have hk' : k < n := by omega
        apply functor_ext_rectangle
        · intro a x
          have he : endGlobe (pasteCylinder (Nat.lt_trans hkl hl)
              (pasteCylinder hl F F' h) (pasteCylinder hl G G' i) ee) a =
            endGlobe (pasteCylinder hl (pasteCylinder (Nat.lt_trans hkl hl) F G e)
              (pasteCylinder (Nat.lt_trans hkl hl) F' G' j) hh) a := by
            apply GlobeComplex.functor_ext
            change (pasteCylinder (by omega) _ _ ee).map (atEnd a (topTable (n+1))) =
              (pasteCylinder (by omega) _ _ hh).map (atEnd a (topTable (n+1)))
            simp only [pasteCylinder_endpoint_top]
            exact Y.join_interchange (k+1) (l+1) hkl _ _ _ _
              (h.ends a) (i.ends a) (e.ends a) (j.ends a)
          exact congrArg (fun Q => Q.map x) he
        · intro a
          simp only [pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hl']
        · intro x
          rw [pasteCylinder_succ_up hk', pasteCylinder_succ_up hl']
          open PositiveInterchange in
          have hlhs := pasteCylinder_val_congr hk'
            (rectangleDiagramOfFunctor (pasteCylinder hl F F' h)).diagonal
            (CylinderComposition.secondDiagonal (pasteCylinder hl F F' h) (pasteCylinder hl G G' i) ee)
            (CylinderComposition.diagonal_matching _ _ ee)
            (pasteCylinder hl' (A F) (C F F' h) (AC F F' h))
            (pasteCylinder hl' (B F G e) (Z F G G' e i) (BZ F G G' e i))
            (outer_e F G F' G' e h i hl' ee)
            (fun z => pasteCylinder_succ_up hl' F F' h z) (fun z => (BZ_map F G G' e i hl' z).symm) x
          open PositiveInterchange in
          have hrhs := pasteCylinder_val_congr hl'
            (rectangleDiagramOfFunctor (pasteCylinder (Nat.lt_trans hkl hl) F G e)).diagonal
            (CylinderComposition.secondDiagonal (pasteCylinder (Nat.lt_trans hkl hl) F G e)
              (pasteCylinder (Nat.lt_trans hkl hl) F' G' j) hh)
            (CylinderComposition.diagonal_matching _ _ hh)
            (pasteCylinder hk' (A F) (B F G e) (AB F G e))
            (pasteCylinder hk' (C F F' h) (Z F G G' e i) (CZ F G F' G' e j h i))
            (outer_h F G F' G' e j h i hk' hh)
            (fun z => pasteCylinder_succ_up hk' F G e z) (fun z => (CZ_map F G F' G' e j h i hk' z).symm) x
          open PositiveInterchange in
          have hi := ih n l hkl' hl' (A F) (B F G e) (C F F' h) (Z F G G' e i)
            (AB F G e) (CZ F G F' G' e j h i) (AC F F' h) (BZ F G G' e i)
            (outer_e F G F' G' e h i hl' ee) (outer_h F G F' G' e j h i hk' hh)
          exact hlhs.trans ((congrArg (fun Q => (Q.map x).val) hi).trans hrhs.symm)
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma restrictCylinder_from_zero_endpoint {m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) (b a : Bool) (x : Table (complex.{u} m)) :
    (restrictCylinder m b F).map (atEnd a x) = F.map (atEnd a (topTable 0)) := by
  rw [restrictCylinder_endpoint, globe_zero_unique ((faceMap 0 m b).nu.map x)]

lemma restrictCylinder_from_zero_edge {m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) (b a : Bool) :
    (restrictCylinder (m+1) b F).map (verticalTable (vertex m a)) = F.map (verticalTable (topTable 0)) := by
  change F.map ((faceMap 0 (m+1) b).cylinder.nu.map (verticalTable (vertex m a))) = _
  rw [verticalTable_natural, globe_zero_unique ((faceMap 0 (m+1) b).nu.map (vertex m a))]

lemma restrictCylinder_from_zero_up {m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) (b : Bool) (x : Table (K.{u} m)) :
    (restrictCylinder (m+1) b F).map (up x) = F.map (verticalTable (topTable 0)) := by
  change F.map ((faceMap 0 (m+1) b).cylinder.nu.map (up x)) = _
  rw [tensorFace_zero_up]

lemma concatInterval_map_of_const {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (y : Y.Cell)
    (he : ∀ x, F.map x = y) (hf : ∀ x, G.map x = y) (x : Table (K.{u} n)) :
    (concatInterval F G h).map x = y := by
  have hy : Y.source 0 y = y := by
    erw [← he x, ← F.map_source, he, he]
  have hF : F = constantAt (K n).nu y hy := OmegaCategory.Functor.ext (funext he)
  have hG : G = constantAt (K n).nu y hy := OmegaCategory.Functor.ext (funext hf)
  subst F G
  rw [concatInterval_constantAt]
  rfl

lemma concatInterval_const_val {n : ℕ} {Y : OmegaCategory.{v}} {a b : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G) (y : Y.Cell)
    (he : ∀ x, (F.map x).val = y) (hf : ∀ x, (G.map x).val = y) (x : Table (K.{u} n)) :
    ((concatInterval F G h).map x).val = y := by
  let z := F.map (atEnd false (topTable n))
  have hF (w) : F.map w = z := Subtype.ext ((he w).trans (he _).symm)
  have hG (w) : G.map w = z := Subtype.ext ((hf w).trans (he _).symm)
  exact (congrArg Subtype.val (concatInterval_map_of_const F G h z hF hG x)).trans (he _)

lemma concatInterval_restrict (n m : ℕ) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (b : Bool) :
    restrictCylinder m b (concatInterval F G h) =
      concatInterval (restrictCylinder m b F) (restrictCylinder m b G) (h.restrict m b) := by
  induction m generalizing n Y with
  | zero =>
    cases n with
    | zero => simp only [restrictCylinder_self]
    | succ n =>
      apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · erw [he, restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · rw [he]
        change (concatInterval F G h).map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))) = _
        rw [verticalTable_natural, faceMap_top]
        change (concatInterval F G h).map (verticalTable (vertex n b)) = _
        rw [concatInterval_succ_edge, concatInterval_zero_vertical]
        change _ = Y.join 0
          (F.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
          (G.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
        rw [verticalTable_natural, faceMap_top]
        rfl
  | succ m ih =>
    cases n with
    | zero =>
      apply functor_ext_rectangle
      · intro a x
        rw [restrictCylinder_from_zero_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_from_zero_endpoint]
      · intro a
        rw [restrictCylinder_from_zero_edge, concatInterval_zero_vertical, concatInterval_succ_edge,
          restrictCylinder_from_zero_edge, restrictCylinder_from_zero_edge]
      · intro x
        rw [restrictCylinder_from_zero_up, concatInterval_zero_vertical, concatInterval_succ_up]
        symm
        apply concatInterval_const_val
        · intro z
          change Y.join 0 ((restrictCylinder (m+1) b F).map (verticalTable (vertex m false)))
            ((restrictCylinder (m+1) b G).map (up z)) = _
          erw [restrictCylinder_from_zero_edge, restrictCylinder_from_zero_up]
        · intro z
          change Y.join 0 ((restrictCylinder (m+1) b F).map (up z))
            ((restrictCylinder (m+1) b G).map (verticalTable (vertex m true))) = _
          erw [restrictCylinder_from_zero_up, restrictCylinder_from_zero_edge]
    | succ n =>
      apply functor_ext_rectangle
      · intro a x
        erw [restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · intro a
        simp only [restrictCylinder_edge, concatInterval_succ_edge]
      · intro x
        erw [restrictCylinder_up, concatInterval_succ_up, concatInterval_succ_up]
        let D := rectangleDiagramOfFunctor F
        let E := rectangleDiagramOfFunctor G
        have he := ih n (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h)
          (D.concatDiagonal_matching E h)
        have hl := congrArg (fun P => (P.map x).val) he
        refine hl.trans (concatInterval_val_congr
          (restrictCylinder m b (D.concatDiagonalOne E h))
          (restrictCylinder m b (D.concatDiagonalTwo E h)) _
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalOne
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b))
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalTwo
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b)) _ ?_ ?_ x)
        · intro z
          change Y.join 0 (F.map (verticalTable (vertex n false)))
            (G.map (up ((faceMap n m b).cylinder.nu.map z))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (verticalTable (vertex m false)))
                ((restrictCylinder (m+1) b G).map (up z))
          erw [restrictCylinder_edge, restrictCylinder_up]
        · intro z
          change Y.join 0 (F.map (up ((faceMap n m b).cylinder.nu.map z)))
            (G.map (verticalTable (vertex n true))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (up z))
                ((restrictCylinder (m+1) b G).map (verticalTable (vertex m true)))
          erw [restrictCylinder_up, restrictCylinder_edge]

lemma pasteCylinder_restrict_gt (n k i : ℕ) (hk : k < n) (hki : k < i)
    {Y : OmegaCategory.{v}} (F G : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : FaceMatching k F G) (b : Bool) :
    restrictCylinder i b (pasteCylinder hk F G h) =
      pasteCylinder hki (restrictCylinder i b F) (restrictCylinder i b G) (h.restrict hki b) := by
  induction k generalizing n i Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => omega
      | succ i =>
        apply functor_ext_rectangle
        · intro a x
          have he : endGlobe (restrictCylinder (i+1) b (pasteCylinder hk F G h)) a =
              endGlobe (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)) a := by
            apply GlobeComplex.functor_ext
            change (restrictCylinder (i+1) b (pasteCylinder hk F G h)).map (atEnd a (topTable (i+1))) =
              (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)).map (atEnd a (topTable (i+1)))
            rw [restrictCylinder_endpoint_top, pasteCylinder_endpoint_top, pasteCylinder_endpoint_top,
              restrictCylinder_endpoint_top, restrictCylinder_endpoint_top]
            cases b
            · exact Y.join_source_gt (i+1) 0 _ _ hki (h.ends a)
            · exact Y.join_target_gt (i+1) 0 _ _ hki (h.ends a)
          exact congrArg (fun P => P.map x) he
        · intro a
          rw [restrictCylinder_edge, pasteCylinder_zero_edge, pasteCylinder_zero_edge]
          cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_edge]
        · intro x
          erw [restrictCylinder_up, pasteCylinder_zero_up, pasteCylinder_zero_up]
          let D := rectangleDiagramOfFunctor F
          let E := rectangleDiagramOfFunctor G
          have he := concatInterval_restrict n i (D.horizontalDiagonalOne E (zeroFaceMatching_seam h))
            (D.horizontalDiagonalTwo E (zeroFaceMatching_seam h))
            (D.horizontalDiagonal_matching E (zeroFaceMatching_seam h)) b
          have hv := congrArg (fun P => (P.map x).val) he
          refine hv.trans (concatInterval_val_congr _ _ _ _ _ _ ?_ ?_ x)
          · intro z
            change Y.join 0 (F.map (up ((faceMap n i b).cylinder.nu.map z)))
              (G.map (atEnd true (suspendTable (project ((faceMap n i b).cylinder.nu.map z))))) =
                Y.join 0 ((restrictCylinder (i+1) b F).map (up z))
                  ((restrictCylinder (i+1) b G).map (atEnd true (suspendTable (project z))))
            erw [restrictCylinder_up, restrictCylinder_endpoint, faceMap_suspend, tensorFace_project]
          · intro z
            change Y.join 0 (F.map (atEnd false (suspendTable (project ((faceMap n i b).cylinder.nu.map z)))))
              (G.map (up ((faceMap n i b).cylinder.nu.map z))) =
                Y.join 0 ((restrictCylinder (i+1) b F).map (atEnd false (suspendTable (project z))))
                  ((restrictCylinder (i+1) b G).map (up z))
            erw [restrictCylinder_endpoint, faceMap_suspend, restrictCylinder_up, tensorFace_project]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => omega
      | succ i =>
        have hk' : k < n := by omega
        have hki' : k < i := by omega
        apply functor_ext_rectangle
        · intro a x
          have he : endGlobe (restrictCylinder (i+1) b (pasteCylinder hk F G h)) a =
              endGlobe (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)) a := by
            apply GlobeComplex.functor_ext
            change (restrictCylinder (i+1) b (pasteCylinder hk F G h)).map (atEnd a (topTable (i+1))) =
              (pasteCylinder hki (restrictCylinder (i+1) b F)
                (restrictCylinder (i+1) b G) (h.restrict hki b)).map (atEnd a (topTable (i+1)))
            rw [restrictCylinder_endpoint_top, pasteCylinder_endpoint_top, pasteCylinder_endpoint_top,
              restrictCylinder_endpoint_top, restrictCylinder_endpoint_top]
            cases b
            · exact Y.join_source_gt (i+1) (k+1) _ _ hki (h.ends a)
            · exact Y.join_target_gt (i+1) (k+1) _ _ hki (h.ends a)
          exact congrArg (fun P => P.map x) he
        · intro a
          rw [restrictCylinder_edge, pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hki',
            restrictCylinder_edge]
        · intro x
          erw [restrictCylinder_up, pasteCylinder_succ_up hk', pasteCylinder_succ_up hki']
          have he := ih n i hk' hki' (rectangleDiagramOfFunctor F).diagonal
            (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
          have hv := congrArg (fun P => (P.map x).val) he
          refine hv.trans (pasteCylinder_val_congr hki' _ _ _ _ _ _ ?_ ?_ x)
          · intro z
            change F.map (up ((faceMap n i b).cylinder.nu.map z)) = (restrictCylinder (i+1) b F).map (up z)
            exact (restrictCylinder_up F b z).symm
          · intro z
            change G.map (up ((faceMap n i b).cylinder.nu.map z)) = (restrictCylinder (i+1) b G).map (up z)
            exact (restrictCylinder_up G b z).symm
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace GlobeComplex
lemma faceMap_above (n m : ℕ) (hnm : n ≤ m) (b : Bool) :
    faceMap.{u} n m b = faceMap n m false := by
  apply hom_ext
  rw [faceMap_top, faceMap_top]
  rw [← face_nu, ← face_nu]
  change (complex n).nu.face m b (topTable n) = (complex n).nu.source m (topTable n)
  rw [(complex n).nu.face_of_fixed (topTable_bounded n) hnm b,
    (complex n).nu.source_fixed_upwards hnm (topTable_bounded n)]

lemma faceMap_faceMap_above (n m j : ℕ) (hnm : n ≤ m) (a b : Bool) :
    Hom.comp (faceMap.{u} m j a) (faceMap n m b) = faceMap n j a := by
  apply hom_ext
  change (faceMap n m b).nu.map ((faceMap m j a).nu.map (topTable j)) = _
  rw [faceMap_top]
  change (faceMap n m b).table (truncate j a (topTable m)) = _
  rw [Hom.table_truncate]
  change truncate j a ((faceMap n m b).nu.map (topTable m)) = _
  rw [faceMap_top, faceMap_top]
  have ht : truncate m b (topTable n) = topTable n := by
    rw [← face_nu]
    exact (complex n).nu.face_of_fixed (topTable_bounded n) hnm b
  rw [ht]
end GlobeComplex

namespace GrayRecursive
lemma restrictCylinder_above {n m : ℕ} (h : n ≤ m) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b : Bool) :
    restrictCylinder m b F = restrictCylinder m false F := by
  unfold restrictCylinder
  rw [faceMap_above n m h b]

lemma restrictCylinder_restrict_above {n m j : ℕ} (h : n ≤ m) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a b : Bool) :
    restrictCylinder j a (restrictCylinder m b F) = restrictCylinder j a F := by
  apply OmegaCategory.Functor.ext
  funext x
  change F.map ((faceMap n m b).cylinder.nu.map ((faceMap m j a).cylinder.nu.map x)) = _
  have hc := congrArg (fun f => f.cylinder.nu.map x) (faceMap_faceMap_above n m j h a b)
  rw [Hom.cylinder_comp] at hc
  exact congrArg F.map hc

lemma restrictCylinder_twice {n m j : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a b : Bool) :
    restrictCylinder j a (restrictCylinder m b F) =
      if j < m then restrictCylinder j a F else restrictCylinder j false (restrictCylinder m b F) := by
  by_cases hj : j < m
  · rw [ite_eq_left hj, restrictCylinder_restrict hj]
  · rw [ite_eq_right hj]
    exact restrictCylinder_above (by omega) _ a
end GrayRecursive
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable (Y : OmegaCategory.{u})

def Cell := {f : ∀ n, OmegaCategory.Functor (K.{u} n).nu Y //
  ∃ N, ∀ n, f n = restrictCylinder n false (f N)}

variable {Y}

def ofMap {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) : Cell Y :=
  ⟨fun m => restrictCylinder m false F, n, fun m => by dsimp only; rw [restrictCylinder_self]⟩

def eval (n : ℕ) (x : Cell Y) : OmegaCategory.Functor (K.{u} n).nu Y := x.val n

@[simp] lemma eval_ofMap {n m : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    eval m (ofMap F) = restrictCylinder m false F := rfl

@[simp] lemma eval_ofMap_self {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    eval n (ofMap F) = F := restrictCylinder_self F false

lemma ofMap_injective (n : ℕ) : Function.Injective (@ofMap Y n) := by
  intro F G h
  have he := congrArg (eval n) h
  simpa only [eval_ofMap_self] using he

lemma ofMap_raise {n m : ℕ} (h : n ≤ m) (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    ofMap (restrictCylinder m false F) = ofMap F := by
  apply Subtype.ext
  funext j
  exact restrictCylinder_restrict_above h F false false

def Bounded (n : ℕ) (x : Cell Y) : Prop := ofMap (eval n x) = x

lemma ofMap_bounded {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    Bounded n (ofMap F) := by simp only [Bounded, eval_ofMap_self]

lemma bounded_exists (x : Cell Y) : ∃ N, Bounded N x := by
  obtain ⟨N,hN⟩ := x.property
  exact ⟨N, Subtype.ext (funext fun n => (hN n).symm)⟩

def bound (x : Cell Y) : ℕ := (bounded_exists x).choose

lemma bounded_bound (x : Cell Y) : Bounded (bound x) x := (bounded_exists x).choose_spec

lemma eval_eq_restrict {n : ℕ} {x : Cell Y} (h : Bounded n x) (m : ℕ) :
    eval m x = restrictCylinder m false (eval n x) := by
  exact (congrArg (eval m) h).symm

lemma Bounded.mono {n m : ℕ} {x : Cell Y} (h : Bounded n x) (hnm : n ≤ m) :
    Bounded m x := by
  change ofMap (eval m x) = x
  rw [eval_eq_restrict h m, ofMap_raise hnm]
  exact h

lemma cell_ext {n : ℕ} {x y : Cell Y} (hx : Bounded n x) (hy : Bounded n y)
    (he : eval n x = eval n y) : x = y := by
  rw [← hx, ← hy, he]

def face (m : ℕ) (b : Bool) (x : Cell Y) : Cell Y :=
  ofMap (restrictCylinder m b (eval (bound x) x))

lemma face_eq_of_bounded {n : ℕ} {x : Cell Y} (h : Bounded n x) (m : ℕ) (b : Bool) :
    face m b x = ofMap (restrictCylinder m b (eval n x)) := by
  let N := max n (bound x)
  have hn : n ≤ N := le_max_left _ _
  have hb : bound x ≤ N := le_max_right _ _
  have he : restrictCylinder m b (eval (bound x) x) = restrictCylinder m b (eval n x) := by
    calc
      _ = restrictCylinder m b (eval N x) := by
        rw [eval_eq_restrict (bounded_bound x) N, restrictCylinder_restrict_above hb]
      _ = _ := by rw [eval_eq_restrict h N, restrictCylinder_restrict_above hn]
  exact congrArg ofMap he

@[simp] lemma face_ofMap {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y)
    (m : ℕ) (b : Bool) : face m b (ofMap F) = ofMap (restrictCylinder m b F) := by
  rw [face_eq_of_bounded (ofMap_bounded F), eval_ofMap_self]

lemma face_bounded (x : Cell Y) (m : ℕ) (b : Bool) : Bounded m (face m b x) :=
  ofMap_bounded _

lemma face_face (x : Cell Y) (i j : ℕ) (a b : Bool) :
    face i a (face j b x) = if i < j then face i a x else face j b x := by
  rw [← bounded_bound x, face_ofMap, face_ofMap]
  by_cases hij : i < j
  · rw [ite_eq_left hij, restrictCylinder_restrict hij, face_ofMap]
  · rw [ite_eq_right hij, restrictCylinder_above (by omega), ofMap_raise (by omega)]

lemma fixed_face {n : ℕ} {x : Cell Y} (h : Bounded n x) (b : Bool) : face n b x = x := by
  rw [face_eq_of_bounded h, restrictCylinder_self]
  exact h

lemma face_bound (x : Cell Y) (b : Bool) : face (bound x) b x = x := fixed_face (bounded_bound x) b

lemma face_represent {n k : ℕ} (hk : k ≤ n) (F : OmegaCategory.Functor (K.{u} n).nu Y)
    (b : Bool) : face k b (ofMap F) = ofMap (faceIdentityCylinder k b F) := by
  rw [face_ofMap]
  exact (ofMap_raise hk _).symm

lemma face_matching {n k : ℕ} {F G : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : face k true (ofMap F) = face k false (ofMap G)) : FaceMatching k F G := by
  have he := (ofMap_injective k) (by simpa only [face_ofMap] using h)
  exact fun x => congrArg (fun P => P.map x) he

lemma face_matching_iff {n k : ℕ} {F G : OmegaCategory.Functor (K.{u} n).nu Y} :
    face k true (ofMap F) = face k false (ofMap G) ↔ FaceMatching k F G := by
  refine ⟨face_matching, fun h => ?_⟩
  rw [face_ofMap, face_ofMap]
  apply congrArg ofMap
  exact OmegaCategory.Functor.ext (funext h)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {Y : OmegaCategory.{u}}

lemma matching_eval {k n : ℕ} {x y : Cell Y} (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) : FaceMatching k (eval n x) (eval n y) := by
  apply face_matching
  change ofMap (eval n x) = x at hx
  change ofMap (eval n y) = y at hy
  simpa only [hx,hy] using h

def composeAt (k n : ℕ) (hk : k < n) (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) : Cell Y :=
  ofMap (pasteCylinder hk (eval n x) (eval n y) (matching_eval hx hy h))

lemma composeAt_bounded (k n : ℕ) (hk : k < n) (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) : Bounded n (composeAt k n hk x y hx hy h) :=
  ofMap_bounded _

lemma ofMap_paste_raise {k n m : ℕ} (hk : k < n) (hnm : n ≤ m)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) :
    ofMap (pasteCylinder hk F G h) = ofMap
      (pasteCylinder (Nat.lt_of_lt_of_le hk hnm) (restrictCylinder m false F) (restrictCylinder m false G)
        (h.restrict (Nat.lt_of_lt_of_le hk hnm) false)) := by
  rw [← pasteCylinder_restrict_gt n k m hk (Nat.lt_of_lt_of_le hk hnm), ofMap_raise hnm]

lemma composeAt_mono {k n m : ℕ} (hk : k < n) (hnm : n ≤ m)
    (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (h : face k true x = face k false y) :
    composeAt k n hk x y hx hy h = composeAt k m (Nat.lt_of_lt_of_le hk hnm) x y
      (hx.mono hnm) (hy.mono hnm) h := by
  unfold composeAt
  rw [ofMap_paste_raise hk hnm]
  congr 1
  have ex := eval_eq_restrict hx m
  have ey := eval_eq_restrict hy m
  simp only [ex,ey]

lemma composeAt_independent {k n m : ℕ} (hkn : k < n) (hkm : k < m)
    (x y : Cell Y) (hx : Bounded n x) (hy : Bounded n y)
    (hx' : Bounded m x) (hy' : Bounded m y)
    (h : face k true x = face k false y) :
    composeAt k n hkn x y hx hy h = composeAt k m hkm x y hx' hy' h := by
  rw [composeAt_mono hkn (le_max_left n m), composeAt_mono hkm (le_max_right n m)]

def comp (k : ℕ) (x y : Cell Y) (h : face k true x = face k false y) : Cell Y :=
  let N := max (k+1) (max (bound x) (bound y))
  composeAt k N (by omega) x y
    ((bounded_bound x).mono (by omega)) ((bounded_bound y).mono (by omega)) h

lemma comp_eq_composeAt {k n : ℕ} (hk : k < n) (x y : Cell Y)
    (hx : Bounded n x) (hy : Bounded n y) (h : face k true x = face k false y) :
    comp k x y h = composeAt k n hk x y hx hy h :=
  composeAt_independent (by omega) hk x y
    ((bounded_bound x).mono (by omega)) ((bounded_bound y).mono (by omega)) hx hy h

lemma comp_ofMap {k n : ℕ} (hk : k < n)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : face k true (ofMap F) = face k false (ofMap G)) :
    comp k (ofMap F) (ofMap G) h = ofMap (pasteCylinder hk F G (face_matching h)) := by
  rw [comp_eq_composeAt hk _ _ (ofMap_bounded F) (ofMap_bounded G)]
  unfold composeAt
  simp only [eval_ofMap_self]

lemma comp_bounded {k n : ℕ} (hk : k < n) (x y : Cell Y)
    (hx : Bounded n x) (hy : Bounded n y) (h : face k true x = face k false y) :
    Bounded n (comp k x y h) := by
  rw [comp_eq_composeAt hk x y hx hy h]
  exact composeAt_bounded k n hk x y hx hy h

lemma face_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Cell Y)
    (h : face k true x = face k false y) (b : Bool) :
    face i b (comp k x y h) = face i b (if b then y else x) := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  rw [comp_ofMap hk, face_ofMap, pasteCylinder_lower_face N k i hk hik]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, face_ofMap]

lemma face_comp_gt (i k : ℕ) (hki : k < i) (x y : Cell Y)
    (h : face k true x = face k false y) (b : Bool)
    (hs : face k true (face i b x) = face k false (face i b y)) :
    face i b (comp k x y h) = comp k (face i b x) (face i b y) hs := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  simp only [face_ofMap] at hs ⊢
  rw [comp_ofMap hk, face_ofMap, pasteCylinder_restrict_gt N k i hk hki, comp_ofMap hki]
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {Y : OmegaCategory.{u}}

lemma comp_left_unit (k : ℕ) (x : Cell Y) (h : face k true (face k false x) = face k false x) :
    comp k (face k false x) x h = x := by
  let N := max (k+1) (bound x)
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  simp only [face_represent (Nat.le_of_lt hk)] at h ⊢
  rw [comp_ofMap hk, pasteCylinder_left_unit]

lemma comp_right_unit (k : ℕ) (x : Cell Y) (h : face k true x = face k false (face k true x)) :
    comp k x (face k true x) h = x := by
  let N := max (k+1) (bound x)
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  simp only [face_represent (Nat.le_of_lt hk)] at h ⊢
  rw [comp_ofMap hk, pasteCylinder_right_unit]

lemma comp_assoc (k : ℕ) (x y z : Cell Y)
    (hxy : face k true x = face k false y) (hyz : face k true y = face k false z)
    (hxy_z : face k true (comp k x y hxy) = face k false z)
    (hx_yz : face k true x = face k false (comp k y z hyz)) :
    comp k (comp k x y hxy) z hxy_z = comp k x (comp k y z hyz) hx_yz := by
  let N := max (k+1) (max (bound x) (max (bound y) (bound z)))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  have hz : Bounded N z := (bounded_bound z).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  obtain ⟨H,rfl⟩ : ∃ H : OmegaCategory.Functor (K.{u} N).nu Y, ofMap H = z := ⟨_,hz⟩
  simp only [comp_ofMap hk] at hxy_z hx_yz ⊢
  congr 1
  apply pasteCylinder_associative

lemma comp_interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell Y)
    (hab : face l true a = face l false b) (hcd : face l true c = face l false d)
    (hac : face k true a = face k false c) (hbd : face k true b = face k false d)
    (hab_cd : face k true (comp l a b hab) = face k false (comp l c d hcd))
    (hac_bd : face l true (comp k a c hac) = face l false (comp k b d hbd)) :
    comp k (comp l a b hab) (comp l c d hcd) hab_cd =
      comp l (comp k a c hac) (comp k b d hbd) hac_bd := by
  let N := max (l+1) (max (bound a) (max (bound b) (max (bound c) (bound d))))
  have hl : l < N := by omega
  have hk : k < N := by omega
  have ha : Bounded N a := (bounded_bound a).mono (by omega)
  have hb : Bounded N b := (bounded_bound b).mono (by omega)
  have hc : Bounded N c := (bounded_bound c).mono (by omega)
  have hd : Bounded N d := (bounded_bound d).mono (by omega)
  clear_value N
  obtain ⟨A,rfl⟩ : ∃ A : OmegaCategory.Functor (K.{u} N).nu Y, ofMap A = a := ⟨_,ha⟩
  obtain ⟨B,rfl⟩ : ∃ B : OmegaCategory.Functor (K.{u} N).nu Y, ofMap B = b := ⟨_,hb⟩
  obtain ⟨C,rfl⟩ : ∃ C : OmegaCategory.Functor (K.{u} N).nu Y, ofMap C = c := ⟨_,hc⟩
  obtain ⟨D,rfl⟩ : ∃ D : OmegaCategory.Functor (K.{u} N).nu Y, ofMap D = d := ⟨_,hd⟩
  simp only [comp_ofMap hk, comp_ofMap hl] at hab_cd hac_bd ⊢
  congr 1
  apply pasteCylinder_interchange N k l hkl hl

def omegaCategory (Y : OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := Cell Y
  source k x := face k false x
  target k x := face k true x
  source_source i j x := by
    rw [face_face]
    split
    · rename_i h
      rw [min_eq_left (le_of_lt h)]
    · rename_i h
      rw [min_eq_right (by omega)]
  target_target i j x := by
    rw [face_face]
    split
    · rename_i h
      rw [min_eq_left (le_of_lt h)]
    · rename_i h
      rw [min_eq_right (by omega)]
  source_target i j x := face_face x i j false true
  target_source i j x := face_face x i j true false
  comp := comp
  source_comp_le i k hik x y h := face_comp_le i k hik x y h false
  target_comp_le i k hik x y h := face_comp_le i k hik x y h true
  source_comp_gt i k hki x y h hs := face_comp_gt i k hki x y h false hs
  target_comp_gt i k hki x y h ht := face_comp_gt i k hki x y h true ht
  unit_left := comp_left_unit
  unit_right := comp_right_unit
  assoc := comp_assoc
  interchange := comp_interchange
  finite_dimension x := ⟨bound x, face_bound x false⟩
end Thomason.GrayRecursive.IntervalHom

end

end OAI
