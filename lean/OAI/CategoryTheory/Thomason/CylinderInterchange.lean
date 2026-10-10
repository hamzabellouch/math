import Mathlib
import OAI.CategoryTheory.Thomason.StationaryCylinders

namespace OAI

/-! Cylinder Interchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma tensorFace_tensorFace (n k j : ℕ) (hjk : j < k) (a b : Bool)
    (x : Table (K.{u} j)) :
    (faceMap n k b).cylinder.nu.map ((faceMap k j a).cylinder.nu.map x) =
      (faceMap n j a).cylinder.nu.map x := by
  have he := congrArg (fun f => f.cylinder.nu.map x) (faceMap_faceMap n k j hjk a b)
  rw [DirectedComplex.Hom.cylinder_comp] at he
  exact he

lemma restrictCylinder_restrict {n k j : ℕ} (hjk : j < k)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) (a b : Bool) :
    restrictCylinder j a (restrictCylinder k b F) = restrictCylinder j a F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact congrArg F.map (tensorFace_tensorFace n k j hjk a b x)

lemma FaceMatching.restrict {n k i : ℕ} (hki : k < i)
    {Y : OmegaCategory.{v}} {F G : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : FaceMatching k F G) (b : Bool) :
    FaceMatching k (restrictCylinder i b F) (restrictCylinder i b G) := by
  intro x
  change F.map ((faceMap n i b).cylinder.nu.map ((faceMap i k true).cylinder.nu.map x)) =
    G.map ((faceMap n i b).cylinder.nu.map ((faceMap i k false).cylinder.nu.map x))
  rw [tensorFace_tensorFace n i k hki true b, tensorFace_tensorFace n i k hki false b]
  exact h x

lemma FaceMatching.paste_left {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{v}} {F G H : OmegaCategory.Functor (K.{u} n).nu Y}
    (hFG : FaceMatching k F G) (hGH : FaceMatching k G H) :
    FaceMatching k (pasteCylinder hk F G hFG) H := by
  intro x
  have he := congrArg (fun P => P.map x) (pasteCylinder_lower_face n k k hk le_rfl F G hFG true)
  exact he.trans (hGH x)

lemma FaceMatching.paste_right {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{v}} {F G H : OmegaCategory.Functor (K.{u} n).nu Y}
    (hFG : FaceMatching k F G) (hGH : FaceMatching k G H) :
    FaceMatching k F (pasteCylinder hk G H hGH) := by
  intro x
  have he := congrArg (fun P => P.map x) (pasteCylinder_lower_face n k k hk le_rfl G H hGH false)
  exact (hFG x).trans he.symm

lemma tensorFace_project (n m : ℕ) (b : Bool) (x : Table (K.{u} m)) :
    project ((faceMap n m b).cylinder.nu.map x) = (faceMap n m b).nu.map (project x) := by
  exact congrArg (fun f => f.nu.map x) (DirectedComplex.Hom.cylinder_projection (faceMap n m b))

lemma pasteCylinder_upper_face (n k i : ℕ) (hk : k < n) (hki : k < i) (hin : i ≤ n)
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
          have he := concatInterval_face n i (by omega) (D.horizontalDiagonalOne E (zeroFaceMatching_seam h))
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
          have he := ih n i hk' hki' (by omega) (rectangleDiagramOfFunctor F).diagonal
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


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma intervalLabel_natural {n m : ℕ} (f : Hom (complex.{u} n) (complex.{u} m))
    (x : Table (K.{u} n)) (b : Bool) :
    intervalLabel (f.cylinder.nu.map x) b = intervalLabel x b := by
  exact f.map_augmentation ((x.row 0 b).2)

lemma tensorFace_zero_up (n : ℕ) (b : Bool) (x : Table (K.{u} n)) :
    (faceMap 0 (n+1) b).cylinder.nu.map (up x) = verticalTable (topTable 0) := by
  rcases table_zero_cases ((faceMap 0 (n+1) b).cylinder.nu.map (up x)) with ⟨a,he⟩ | he
  · have hs := congrArg (fun t => intervalLabel t false) he
    have ht := congrArg (fun t => intervalLabel t true) he
    simp only [intervalLabel_natural, intervalLabel_up, intervalLabel_end] at hs ht
    cases a <;> simp_all
  · exact he

def faceIdentityCylinder {n : ℕ} (k : ℕ) (b : Bool) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) : OmegaCategory.Functor (K.{u} n).nu Y :=
  restrictCylinder n false (restrictCylinder k b F)

lemma faceIdentityCylinder_endpoint_top {n k : ℕ} (hk : k ≤ n)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) (b a : Bool) :
    (faceIdentityCylinder k b F).map (atEnd a (topTable n)) =
      Y.face k b (F.map (atEnd a (topTable n))) := by
  unfold faceIdentityCylinder
  rw [restrictCylinder_endpoint_top, restrictCylinder_endpoint_top]
  cases b
  · exact Y.source_source n k _ |>.trans (congrArg (fun j => Y.source j _) (min_eq_right hk))
  · change Y.source n (Y.target k _) = Y.target k _
    rw [Y.source_target, ite_eq_right (by omega)]

lemma faceIdentityCylinder_succ_edge {n k : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) :
    (faceIdentityCylinder (k+1) b F).map (verticalTable (vertex n a)) =
      F.map (verticalTable (vertex n a)) := by
  simp only [faceIdentityCylinder, restrictCylinder_edge]

lemma faceIdentityCylinder_succ_up {n k : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) (x : Table (K.{u} n)) :
    (faceIdentityCylinder (k+1) b F).map (up x) =
      ((faceIdentityCylinder k b (rectangleDiagramOfFunctor F).diagonal).map x).val := by
  simp only [faceIdentityCylinder, restrictCylinder_up]
  erw [restrictCylinder_up]
  rfl

lemma faceIdentityCylinder_zero_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) :
    (faceIdentityCylinder 0 b F).map (verticalTable (vertex n a)) =
      F.map (verticalTable (vertex n b)) := by
  change (restrictCylinder 0 b F).map ((faceMap 0 (n+1) false).cylinder.nu.map (verticalTable (vertex n a))) = _
  rw [verticalTable_natural, globe_zero_unique ((faceMap 0 (n+1) false).nu.map (vertex n a))]
  exact restrictCylinder_zero_vertical F b

lemma faceIdentityCylinder_zero_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) (x : Table (K.{u} n)) :
    (faceIdentityCylinder 0 b F).map (up x) = F.map (verticalTable (vertex n b)) := by
  change (restrictCylinder 0 b F).map ((faceMap 0 (n+1) false).cylinder.nu.map (up x)) = _
  rw [tensorFace_zero_up]
  exact restrictCylinder_zero_vertical F b

lemma faceIdentityCylinder_zero_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) (x : Table (complex.{u} (n+1))) :
    (faceIdentityCylinder 0 b F).map (atEnd a x) = F.map (atEnd a (vertex n b)) := by
  change (restrictCylinder 0 b F).map ((faceMap 0 (n+1) false).cylinder.nu.map (atEnd a x)) = _
  rw [cylinderHom_atEnd, globe_zero_unique ((faceMap 0 (n+1) false).nu.map x), restrictCylinder_endpoint, faceMap_top]
  rfl

lemma faceIdentityCylinder_left_matching {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    FaceMatching k (faceIdentityCylinder k false F) F := by
  have he : restrictCylinder k true (faceIdentityCylinder k false F) = restrictCylinder k false F := by
    unfold faceIdentityCylinder
    rw [restrictCylinder_restrict hk, restrictCylinder_self]
  intro x
  exact congrArg (fun P => P.map x) he

lemma faceIdentityCylinder_right_matching {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    FaceMatching k F (faceIdentityCylinder k true F) := by
  have he : restrictCylinder k false (faceIdentityCylinder k true F) = restrictCylinder k true F := by
    unfold faceIdentityCylinder
    rw [restrictCylinder_restrict hk, restrictCylinder_self]
  intro x
  exact (congrArg (fun P => P.map x) he).symm

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma pasteCylinder_left_unit (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    pasteCylinder hk (faceIdentityCylinder k false F) F (faceIdentityCylinder_left_matching hk F) = F := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk (faceIdentityCylinder 0 false F) F
            (faceIdentityCylinder_left_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk (faceIdentityCylinder 0 false F) F
            (faceIdentityCylinder_left_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_left_unit 0 _ _ (Y.source_source_self 0 _) (Y.target_source_self 0 _)
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_zero_edge]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, faceIdentityCylinder_zero_edge]
      · intro x
        rw [pasteCylinder_zero_up]
        refine (concatInterval_val_congr _ _ _ (constantInterval (endGlobe D.diagonal false))
          D.diagonal (stationary_left_matching D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (concatInterval_left_unit D.diagonal))
        · intro z
          change Y.join 0 ((faceIdentityCylinder 0 false F).map (up z))
            (F.map (atEnd true (suspendTable (project z)))) =
              (D.diagonal.map (atEnd false (project z))).val
          erw [faceIdentityCylinder_zero_up, D.left]
          rfl
        · intro z
          change Y.join 0 ((faceIdentityCylinder 0 false F).map (atEnd false (suspendTable (project z))))
            (F.map (up z)) = (D.diagonal.map z).val
          rw [faceIdentityCylinder_zero_endpoint]
          apply Y.join_left_unit 0 _ _ (D.vertex_fixed false false)
          rw [D.vertex_target_fixed false false]
          exact (D.diagonal.map z).property.1.symm
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk (faceIdentityCylinder (k+1) false F) F
            (faceIdentityCylinder_left_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk (faceIdentityCylinder (k+1) false F) F
            (faceIdentityCylinder_left_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_left_unit (k+1) _ _ (Y.source_source_self (k+1) _) (Y.target_source_self (k+1) _)
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_succ_edge hk', faceIdentityCylinder_succ_edge]
      · intro x
        rw [pasteCylinder_succ_up hk']
        refine (pasteCylinder_val_congr hk' _ _ _ (faceIdentityCylinder k false D.diagonal)
          D.diagonal (faceIdentityCylinder_left_matching hk' D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (ih n hk' D.diagonal))
        · intro z
          exact faceIdentityCylinder_succ_up F false z
        · intro z
          rfl

lemma pasteCylinder_right_unit (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    pasteCylinder hk F (faceIdentityCylinder k true F) (faceIdentityCylinder_right_matching hk F) = F := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk F (faceIdentityCylinder 0 true F)
            (faceIdentityCylinder_right_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk F (faceIdentityCylinder 0 true F)
            (faceIdentityCylinder_right_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_right_unit 0 _ _ (Y.source_target_self 0 _) (Y.source_target_self 0 _).symm
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_zero_edge]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, faceIdentityCylinder_zero_edge]
      · intro x
        rw [pasteCylinder_zero_up]
        refine (concatInterval_val_congr _ _ _ D.diagonal
          (constantInterval (endGlobe D.diagonal true)) (stationary_right_matching D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (concatInterval_right_unit D.diagonal))
        · intro z
          change Y.join 0 (F.map (up z))
            ((faceIdentityCylinder 0 true F).map (atEnd true (suspendTable (project z)))) =
              (D.diagonal.map z).val
          rw [faceIdentityCylinder_zero_endpoint]
          apply Y.join_right_unit 0 _ _ (D.vertex_fixed true true)
          exact (D.diagonal.map z).property.2.trans (D.vertex_fixed true true).symm
        · intro z
          change Y.join 0 (F.map (atEnd false (suspendTable (project z))))
            ((faceIdentityCylinder 0 true F).map (up z)) =
              (D.diagonal.map (atEnd true (project z))).val
          erw [faceIdentityCylinder_zero_up, D.right]
          rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let D := rectangleDiagramOfFunctor F
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (pasteCylinder hk F (faceIdentityCylinder (k+1) true F)
            (faceIdentityCylinder_right_matching hk F)) a = endGlobe F a := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk F (faceIdentityCylinder (k+1) true F)
            (faceIdentityCylinder_right_matching hk F)).map (atEnd a (topTable (n+1))) =
              F.map (atEnd a (topTable (n+1)))
          rw [pasteCylinder_endpoint_top, faceIdentityCylinder_endpoint_top (by omega)]
          exact Y.join_right_unit (k+1) _ _ (Y.source_target_self (k+1) _) (Y.source_target_self (k+1) _).symm
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_succ_edge hk']
      · intro x
        rw [pasteCylinder_succ_up hk']
        refine (pasteCylinder_val_congr hk' _ _ _ D.diagonal (faceIdentityCylinder k true D.diagonal)
          (faceIdentityCylinder_right_matching hk' D.diagonal) ?_ ?_ x).trans (congrArg (fun P => (P.map x).val) (ih n hk' D.diagonal))
        · intro z
          rfl
        · intro z
          exact faceIdentityCylinder_succ_up F true z
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory Limits DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma FaceMatching.pair {n k : ℕ} {Y Z : OmegaCategory.{u}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : FaceMatching k F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu Z} (h' : FaceMatching k F' G') :
    FaceMatching k (pairFunctor F F') (pairFunctor G G') := by
  have he : (faceMap n k true).cylinder.nu ≫ pairFunctor F F' =
      (faceMap n k false).cylinder.nu ≫ pairFunctor G G' := by
    apply prod.hom_ext <;> simp only [Category.assoc, pairFunctor, prod.lift_fst, prod.lift_snd]
    · exact OmegaCategory.Functor.ext (funext h)
    · exact OmegaCategory.Functor.ext (funext h')
  exact fun x => congrArg (fun f => f.map x) he

lemma pasteCylinder_pair {n k : ℕ} (hk : k < n) {Y Z : OmegaCategory.{u}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu Z) (h' : FaceMatching k F' G')
    (H : FaceMatching k (pairFunctor F F') (pairFunctor G G')) :
    pasteCylinder hk (pairFunctor F F') (pairFunctor G G') H =
      pairFunctor (pasteCylinder hk F G h) (pasteCylinder hk F' G' h') := by
  apply @prod.hom_ext OmegaCategory.{u} _ ((K n).nu) Y Z _
  · change OmegaCategory.Functor.comp (pasteCylinder hk _ _ H) (prod.fst : Y ⨯ Z ⟶ Y) = _
    rw [pasteCylinder_natural]
    change pasteCylinder hk ((pairFunctor F F') ≫ prod.fst) ((pairFunctor G G') ≫ prod.fst) _ = _
    simp only [pairFunctor, prod.lift_fst]
  · change OmegaCategory.Functor.comp (pasteCylinder hk _ _ H) (prod.snd : Y ⨯ Z ⟶ Z) = _
    rw [pasteCylinder_natural]
    change pasteCylinder hk ((pairFunctor F F') ≫ prod.snd) ((pairFunctor G G') ≫ prod.snd) _ = _
    simp only [pairFunctor, prod.lift_snd]

lemma FaceMatching.homCompose {n k : ℕ} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    {F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)} (h : FaceMatching k F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)} (h' : FaceMatching k F' G') :
    FaceMatching k (OmegaCategory.homCompose F F') (OmegaCategory.homCompose G G') := by
  intro x
  apply Subtype.ext
  change Y.join 0 (F.map ((faceMap n k true).cylinder.nu.map x)).val
    (F'.map ((faceMap n k true).cylinder.nu.map x)).val = _
  rw [h x, h' x]
  rfl

lemma pasteCylinder_homCompose {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h' : FaceMatching k F' G') :
    pasteCylinder hk (homCompose F F') (homCompose G G') (h.homCompose h') =
      homCompose (pasteCylinder hk F G h) (pasteCylinder hk F' G' h') := by
  let P : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ Y.homCategory a c :=
    homCompose (prod.fst : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _) (prod.snd : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _)
  have hp (A : (K.{u} n).nu ⟶ Y.homCategory a b)
      (B : (K.{u} n).nu ⟶ Y.homCategory b c) :
      pairFunctor A B ≫ P = homCompose A B := by
    apply OmegaCategory.Functor.ext
    funext x
    apply Subtype.ext
    change Y.join 0 ((pairFunctor A B ≫ prod.fst).map x).val
      ((pairFunctor A B ≫ prod.snd).map x).val = _
    change Y.join 0 ((prod.lift A B ≫ prod.fst).map x).val ((prod.lift A B ≫ prod.snd).map x).val = _
    rw [prod.lift_fst, prod.lift_snd]
    rfl
  have he := pasteCylinder_natural n k hk (pairFunctor F F') (pairFunctor G G') (h.pair h') P
  change pasteCylinder hk _ _ _ ≫ P = pasteCylinder hk (pairFunctor F F' ≫ P) (pairFunctor G G' ≫ P) _ at he
  simp only [pasteCylinder_pair hk F G h F' G' h', hp] at he
  exact he.symm

lemma FaceMatching.constantAt {n k : ℕ} {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) :
    FaceMatching k (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) :=
  fun _ => rfl

@[simp] lemma pasteCylinder_constantAt {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) (h : FaceMatching k (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha)) :
    pasteCylinder hk (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) h =
      constantAt (K.{u} n).nu a ha := by
  have he : faceIdentityCylinder k false (constantAt (K.{u} n).nu a ha) =
      constantAt (K.{u} n).nu a ha := rfl
  simpa only [he] using pasteCylinder_left_unit n k hk (constantAt (K.{u} n).nu a ha)

lemma pasteCylinder_homCompose_left {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = a) (ht : Y.target 0 f = b)
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : FaceMatching k F G)
    (h' : FaceMatching k (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G)) :
    pasteCylinder hk (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G) h' =
      homCompose (constantHom (K n).nu f hf hs ht) (pasteCylinder hk F G h) := by
  have e := pasteCylinder_homCompose hk (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (FaceMatching.constantAt (k := k) (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf)) F G h
  exact e.trans (congrArg (fun A => homCompose A (pasteCylinder hk F G h))
    (pasteCylinder_constantAt hk (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

lemma pasteCylinder_homCompose_right {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = b) (ht : Y.target 0 f = c)
    (h' : FaceMatching k (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht))) :
    pasteCylinder hk (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht)) h' =
      homCompose (pasteCylinder hk F G h) (constantHom (K n).nu f hf hs ht) := by
  have e := pasteCylinder_homCompose hk F G h (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (FaceMatching.constantAt (k := k) (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf))
  exact e.trans (congrArg (fun B => homCompose (pasteCylinder hk F G h) B)
    (pasteCylinder_constantAt hk (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

lemma FaceMatching.concat {n k : ℕ} (hk : k ≤ n) {Y : OmegaCategory.{v}}
    {F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : FaceMatching k F G) (i : FaceMatching k F' G')
    (t : IntervalMatching F F') (t' : IntervalMatching G G') :
    FaceMatching k (concatInterval F F' t) (concatInterval G G' t') := by
  have he : restrictCylinder k true (concatInterval F F' t) =
      restrictCylinder k false (concatInterval G G' t') := by
    rw [concatInterval_face n k hk, concatInterval_face n k hk]
    have eh : restrictCylinder k true F = restrictCylinder k false G := OmegaCategory.Functor.ext (funext h)
    have ei : restrictCylinder k true F' = restrictCylinder k false G' := OmegaCategory.Functor.ext (funext i)
    simp only [eh, ei]
  exact fun x => congrArg (fun f => f.map x) he

lemma IntervalMatching.paste {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    {F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y}
    (h : IntervalMatching F F') (i : IntervalMatching G G')
    (t : FaceMatching k F G) (t' : FaceMatching k F' G') :
    IntervalMatching (pasteCylinder hk F G t) (pasteCylinder hk F' G' t') := by
  have he : endGlobe (pasteCylinder hk F G t) true = endGlobe (pasteCylinder hk F' G' t') false := by
    apply GlobeComplex.functor_ext
    change (pasteCylinder hk F G t).map (atEnd true (topTable n)) =
      (pasteCylinder hk F' G' t').map (atEnd false (topTable n))
    rw [pasteCylinder_endpoint_top, pasteCylinder_endpoint_top, h, i]
  exact fun x => congrArg (fun f => f.map x) he

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma IntervalMatching.homCompose {n : ℕ} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    {F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)} (h : IntervalMatching F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)} (h' : IntervalMatching F' G') :
    IntervalMatching (OmegaCategory.homCompose F F') (OmegaCategory.homCompose G G') := by
  intro x
  apply Subtype.ext
  change Y.join 0 (F.map (atEnd true x)).val (F'.map (atEnd true x)).val = _
  rw [h x, h' x]
  rfl

lemma concatInterval_shuffle_left {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) :
    concatInterval (homCompose (constantInterval (endGlobe F false)) G)
      (homCompose F (constantInterval (endGlobe G true)))
      ((stationary_left_matching F).homCompose (stationary_right_matching G)) = homCompose F G := by
  rw [concatInterval_homCompose _ _ (stationary_left_matching F) _ _ (stationary_right_matching G),
    concatInterval_left_unit, concatInterval_right_unit]

lemma concatInterval_shuffle_right {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) :
    concatInterval (homCompose F (constantInterval (endGlobe G false)))
      (homCompose (constantInterval (endGlobe F true)) G)
      ((stationary_right_matching F).homCompose (stationary_left_matching G)) = homCompose F G := by
  rw [concatInterval_homCompose _ _ (stationary_right_matching F) _ _ (stationary_left_matching G),
    concatInterval_right_unit, concatInterval_left_unit]

lemma concatInterval_four {n : ℕ} {Y : OmegaCategory.{u}}
    (A B C D : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : IntervalMatching A B) (i : IntervalMatching B C) (j : IntervalMatching C D) :
    concatInterval (concatInterval A B h) (concatInterval C D j) (h.concat_left (i.concat_right j)) =
      concatInterval A (concatInterval (concatInterval B C i) D (i.concat_left j))
        ((h.concat_right i).concat_right (i.concat_left j)) := by
  rw [concatInterval_associative]
  congr 1
  exact (concatInterval_associative n B C D i j).symm

lemma IntervalMatching.of_val {n : ℕ} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d))
    (h : IntervalMatching F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) : IntervalMatching F G := by
  intro x
  apply Subtype.ext
  erw [he, hf]
  exact congrArg Subtype.val (h x)

end Thomason.GrayRecursive

end

end OAI
