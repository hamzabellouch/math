import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Simplicial.SingularCubeNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

namespace OAI

section

/-! # Relative homotopies lift through finite singular cubes -/

namespace Thomason.Construction.RealizedCube

noncomputable section

/-- Regard the homotopy parameter as the first coordinate of one larger cube. -/
def homotopyCube {X : TopCat.{0}} {n : ℕ} {p q : C((Fin n → unitInterval), X)}
    (H : p.Homotopy q) : C((Fin (n+1) → unitInterval), X) :=
  ⟨fun t => H (t 0, Fin.tail t), H.continuous.comp (by fun_prop)⟩

theorem homotopyCube_zero {X : TopCat.{0}} {n : ℕ} {p q : C((Fin n → unitInterval), X)}
    (H : p.Homotopy q) : (homotopyCube H).comp (insertEndpoint n 0 false) = p := by
  apply ContinuousMap.ext
  intro t
  exact H.apply_zero t

theorem homotopyCube_one {X : TopCat.{0}} {n : ℕ} {p q : C((Fin n → unitInterval), X)}
    (H : p.Homotopy q) : (homotopyCube H).comp (insertEndpoint n 0 true) = q := by
  apply ContinuousMap.ext
  intro t
  exact H.apply_one t

theorem homotopyCube_side {X : TopCat.{0}} {x : X} {n : ℕ}
    {p q : GenLoop (Fin (n+1)) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin (n+1))))
    (i : Fin (n+1)) (e : Bool) :
    (homotopyCube H.toHomotopy).comp (insertEndpoint (n+1) i.succ e) =
      ContinuousMap.const _ x := by
  apply ContinuousMap.ext
  intro t
  have ht : (Fin.insertNth i.succ (endpoint e) t : Fin (n+2) → unitInterval) =
      (Fin.cons (t 0) (Fin.insertNth i (endpoint e) (Fin.tail t)) :
        Fin (n+2) → unitInterval) := by
    conv_lhs => rw [← Fin.cons_self_tail t, Fin.insertNth_succ_cons]
  change H ((Fin.insertNth i.succ (endpoint e) t : Fin (n+2) → unitInterval) 0,
    Fin.tail (Fin.insertNth i.succ (endpoint e) t : Fin (n+2) → unitInterval)) = x
  rw [ht]
  have hb : Fin.insertNth i (endpoint e) (Fin.tail t) ∈ Cube.boundary (Fin (n+1)) := by
    refine ⟨i, ?_⟩
    rw [Fin.insertNth_apply_same]
    cases e
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact (H.eq_fst (t 0) hb).trans (p.property _ hb)

/-- The cubical lift preserves a homotopy relative to the entire boundary. -/
def liftLoopHomotopy {X : TopCat.{0}} {x : X} {n : ℕ}
    {p q : GenLoop (Fin (n+1)) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin (n+1)))) :
    (liftLoop n p).val.HomotopyRel (liftLoop n q).val (Cube.boundary (Fin (n+1))) where
  toFun a := liftMap (n+2) (homotopyCube H.toHomotopy) (Fin.cons a.1 a.2)
  continuous_toFun := by
    apply (liftMap (n+2) (homotopyCube H.toHomotopy)).continuous.comp
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd
  map_zero_left t := by
    change liftMap (n+2) (homotopyCube H.toHomotopy) (Fin.insertNth 0 (endpoint false) t) = _
    rw [liftMap_face, homotopyCube_zero]
    rfl
  map_one_left t := by
    change liftMap (n+2) (homotopyCube H.toHomotopy) (Fin.insertNth 0 (endpoint true) t) = _
    rw [liftMap_face, homotopyCube_one]
    rfl
  prop' s t ht := by
    obtain ⟨i, hi⟩ := ht
    obtain ⟨e, he⟩ : ∃ e : Bool, t i = endpoint e := by
      rcases hi with hi | hi
      · exact ⟨false, hi⟩
      · exact ⟨true, hi⟩
    have hf : t = Fin.insertNth i (endpoint e) (Fin.removeNth i t) := by
      rw [← he, Fin.insertNth_self_removeNth]
    change liftMap (n+2) (homotopyCube H.toHomotopy) (Fin.cons s t) = _
    rw [hf, ← Fin.insertNth_succ_cons, liftMap_face, homotopyCube_side, liftMap_const]
    rw [← hf]
    exact (liftLoop n p).property _ ⟨i, hi⟩ |>.symm

/-- The based cube construction is well-defined on homotopy classes. -/
theorem liftLoop_homotopic {X : TopCat.{0}} {x : X} {n : ℕ}
    {p q : GenLoop (Fin (n+1)) X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (liftLoop n p) (liftLoop n q) :=
  ⟨liftLoopHomotopy h.some⟩

end

end Thomason.Construction.RealizedCube

end

section

/-! # A natural section on positive homotopy groups for singular evaluation -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory

noncomputable section

/-- Cubical singular lifting descends through actual relative homotopies. -/
def liftGroup (X : TopCat.{0}) (x : X) (n : ℕ) :
    HomotopyGroup.Pi (n+1) X x →
      HomotopyGroup.Pi (n+1) (SSet.toTop.obj (TopCat.toSSet.obj X)) (singularVertex X x) :=
  Quotient.map (liftLoop n) (fun _ _ h => liftLoop_homotopic h)

/-- Evaluation is a left inverse to this section on the actual homotopy quotient. -/
theorem counit_liftGroup (X : TopCat.{0}) (x : X) (n : ℕ)
    (p : HomotopyGroup.Pi (n+1) X x) :
    HomotopyMaps.basedGroupMap (sSetTopAdj.counit.app X).hom
      (counit_singularVertex X x) (n+1) (liftGroup X x n p) = p := by
  induction p using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    exact liftLoop_evaluation n p t

theorem liftGroup_injective (X : TopCat.{0}) (x : X) (n : ℕ) :
    Function.Injective (liftGroup X x n) :=
  Function.LeftInverse.injective (counit_liftGroup X x n)

/-- Singular cubical maps commute with postcomposition by continuous maps. -/
theorem singularMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (p : C((Fin n → unitInterval), X)) :
    singularMap n (f.hom.comp p) = singularMap n p ≫ TopCat.toSSet.map f := by
  exact sSetTopAdj.homEquiv_naturality_right (TopCat.ofHom (p.comp (coordinates n))) f

/-- The continuous cubical lifting operation is natural in its target space. -/
theorem liftMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (p : C((Fin n → unitInterval), X)) (t : Fin n → unitInterval) :
    (SSet.toTop.map (TopCat.toSSet.map f)).hom (liftMap n p t) =
      liftMap n (f.hom.comp p) t := by
  have h := SSet.toTop.congr_map (singularMap_naturality f n p)
  rw [SSet.toTop.map_comp] at h
  exact (congrArg (fun g => g.hom (sectionMap n t)) h).symm

/-- The section on positive homotopy groups is natural in all continuous maps. -/
theorem liftGroup_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) (n : ℕ)
    (p : HomotopyGroup.Pi (n+1) X x) :
    HomotopyMaps.basedGroupMap (SSet.toTop.map (TopCat.toSSet.map f)).hom
      (singularVertex_naturality f x) (n+1) (liftGroup X x n p) =
      liftGroup Y (f.hom x) n (HomotopyMaps.groupMap f.hom (n+1) x p) := by
  induction p using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    exact liftMap_naturality f (n+1) p.val t

end

end Thomason.Construction.RealizedCube

end

section

/-! # Injectivity of the singular unit and the remaining comparison test -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The adjunction triangle is an actual continuous left inverse to the realized unit. -/
theorem singular_unit_continuous_left_inverse (K : SSet.{0}) :
    (sSetTopAdj.counit.app (SSet.toTop.obj K)).hom.comp
      (SSet.toTop.map (sSetTopAdj.unit.app K)).hom = ContinuousMap.id _ :=
  congrArg TopCat.Hom.hom (sSetTopAdj.left_triangle_components K)

/-- The realized unit is injective on every positive homotopy group. -/
theorem singular_unit_groupMap_injective (K : SSet.{0})
    (x : SSet.toTop.obj K) (n : ℕ) :
    Function.Injective (HomotopyMaps.groupMap
      (SSet.toTop.map (sSetTopAdj.unit.app K)).hom (n+1) x) := by
  have he := singular_unit_continuous_left_inverse K
  have hx := congrArg (fun f => f x) he
  have h : Function.LeftInverse
      (HomotopyMaps.basedGroupMap (sSetTopAdj.counit.app (SSet.toTop.obj K)).hom hx (n+1))
      (HomotopyMaps.groupMap (SSet.toTop.map (sSetTopAdj.unit.app K)).hom (n+1) x) := by
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      apply congrArg (Quotient.mk _)
      apply GenLoop.ext
      intro t
      exact congrArg (fun f => f (q t)) he
  exact h.injective

/-- The realized unit is already bijective on path components. -/
theorem singular_unit_components_bijective (K : SSet.{0}) :
    Function.Bijective (HomotopyMaps.componentsMap
      (SSet.toTop.map (sSetTopAdj.unit.app K)).hom) := by
  have h := congrArg HomotopyMaps.componentsMap (singular_unit_continuous_left_inverse K)
  rw [HomotopyMaps.componentsMap_comp, HomotopyMaps.componentsMap_id] at h
  apply ((singular_counit_components_bijective (SSet.toTop.obj K)).of_comp_iff' _).mp
  rw [h]
  exact Function.bijective_id

/-- Only surjectivity in positive degrees remains in the unit weak-equivalence test. -/
theorem singular_unit_weak_iff_groupMap_surjective (K : SSet.{0}) :
    realizationWeakEquivalences (sSetTopAdj.unit.app K) ↔
      ∀ (n : ℕ) (x : SSet.toTop.obj K), Function.Surjective (HomotopyMaps.groupMap
        (SSet.toTop.map (sSetTopAdj.unit.app K)).hom (n+1) x) := by
  constructor
  · intro h n x
    exact (h.2 n x).2
  · intro h
    exact ⟨singular_unit_components_bijective K,
      fun n x => ⟨singular_unit_groupMap_injective K x n, h n x⟩⟩

/-- Dually, only positive-degree injectivity remains for the singular counit. -/
theorem singular_counit_weak_iff_groupMap_injective (X : TopCat.{0}) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app X) ↔
      ∀ (n : ℕ) (x : SSet.toTop.obj (TopCat.toSSet.obj X)),
        Function.Injective (HomotopyMaps.groupMap (sSetTopAdj.counit.app X).hom (n+1) x) := by
  constructor
  · intro h n x
    exact (h.2 n x).1
  · intro h
    exact ⟨singular_counit_components_bijective X,
      fun n x => ⟨h n x, singular_counit_groupMap_surjective X x n⟩⟩

end

end Thomason.Construction

end

section

/-! # The singular comparison is weak on each finite cubical local model -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- The actual realization of each finite simplicial cube is contractible. -/
theorem realization_contractible (n : ℕ) : ContractibleSpace (SSet.toTop.obj (obj n)) := by
  induction n with
  | zero => exact standard_simplex_realization_contractible 0
  | succ n ih =>
    let : ContractibleSpace (SSet.toTop.obj (obj n)) := ih
    let e := realizationHomotopyEquiv (fst (obj n) Δ[1]) SSet.ι₀
      (cylinderMinHomotopy (obj n)) (by
        rw [SSet.ι₀_fst]
        exact SSet.RelativeMorphism.Homotopy.refl _)
    exact e.contractibleSpace

/-- Every finite cubical local model satisfies the genuine singular-unit weak test. -/
theorem singular_unit_weak (n : ℕ) :
    realizationWeakEquivalences (sSetTopAdj.unit.app (obj n)) := by
  let := realization_contractible n
  exact singular_unit_weak_contractible _

/-- The actual evaluation counit is weak on each realized finite cubical local model. -/
theorem singular_counit_weak (n : ℕ) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app (SSet.toTop.obj (obj n))) := by
  let := realization_contractible n
  exact singular_counit_weak_contractible _

end

end Thomason.Construction.RealizedCube

end

section

/-! # Singular realization reflects actual weak homotopy equivalences

The natural cubical section and evaluation make each original positive
homotopy-group map a retract of its singular-realization counterpart.
No general counit weak equivalence is used.
-/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Evaluation commutes with the actual based group maps at singular vertices. -/
theorem singular_counit_group_naturality {X Y : TopCat.{0}} (p : X ⟶ Y)
    (x : X) (n : ℕ)
    (a : HomotopyGroup.Pi (n+1) (SSet.toTop.obj (TopCat.toSSet.obj X))
      (singularVertex X x)) :
    HomotopyMaps.groupMap p.hom (n+1) x
      (HomotopyMaps.basedGroupMap (sSetTopAdj.counit.app X).hom
        (counit_singularVertex X x) (n+1) a) =
    HomotopyMaps.basedGroupMap (sSetTopAdj.counit.app Y).hom
      (counit_singularVertex Y (p.hom x)) (n+1)
      (HomotopyMaps.basedGroupMap (SSet.toTop.map (TopCat.toSSet.map p)).hom
        (singularVertex_naturality p x) (n+1) a) := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    exact (congrArg (fun f => f.hom (a.val t)) (sSetTopAdj.counit.naturality p)).symm

/-- Bijectivity on a positive homotopy group is reflected by singular
realization, through the natural section and evaluation retraction. -/
theorem singular_groupMap_bijective_reflects {X Y : TopCat.{0}} (p : X ⟶ Y)
    (x : X) (n : ℕ)
    (hp : Function.Bijective
      (HomotopyMaps.basedGroupMap (SSet.toTop.map (TopCat.toSSet.map p)).hom
        (singularVertex_naturality p x) (n+1))) :
    Function.Bijective (HomotopyMaps.groupMap p.hom (n+1) x) := by
  constructor
  · intro a b hab
    apply RealizedCube.liftGroup_injective X x n
    apply hp.1
    rw [RealizedCube.liftGroup_naturality, RealizedCube.liftGroup_naturality, hab]
  · intro q
    obtain ⟨a, ha⟩ := hp.2 (RealizedCube.liftGroup Y (p.hom x) n q)
    refine ⟨HomotopyMaps.basedGroupMap (sSetTopAdj.counit.app X).hom
      (counit_singularVertex X x) (n+1) a, ?_⟩
    rw [singular_counit_group_naturality, ha, RealizedCube.counit_liftGroup]

/-- The actual realization weak-equivalence test on the singular map implies
that the original continuous map is a weak homotopy equivalence. -/
theorem singular_realization_reflects_weak {X Y : TopCat.{0}} (p : X ⟶ Y)
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    IsWeakHomotopyEquivalence p.hom := by
  refine ⟨(singular_map_components_bijective_iff p).mp hp.1, fun n x => ?_⟩
  apply singular_groupMap_bijective_reflects p x n
  exact (HomotopyMaps.basedGroupMap_bijective_iff _
    (singularVertex_naturality p x) (n+1)).mpr (hp.2 n (singularVertex X x))

end

end Thomason.Construction

end

section

/-! # Units, associativity and face compatibility after intelligent truncation -/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

variable {C : StrictOmegaCategory.{0}} {n : ℕ}

@[simp] theorem comp_of_le {m : ℕ} (hm : n ≤ m) (x y : Cell C n)
    (h : face true m x = face false m y) : comp m x y h = x := by
  simp only [comp, dite_eq_right (show ¬m < n by omega)]

theorem comp_congr (m : ℕ) {x y x' y' : Cell C n} (hx : x = x') (hy : y = y')
    (h : face true m x = face false m y) (h' : face true m x' = face false m y') :
    comp m x y h = comp m x' y' h' := by
  subst x' y'
  rfl

theorem left_unit (m : ℕ) (x : Cell C n)
    (h : face true m (face false m x) = face false m x) :
    comp m (face false m x) x h = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    by_cases hm : m < n
    · have hc := (C.bounded n).face_face_same true false m x
      exact (comp_mk m ((C.bounded n).face false m x) x hc h).trans
        (congrArg mk ((C.bounded n).left_unit m x hc))
    · have hn : n ≤ m := by omega
      rw [comp_of_le hn, face_of_le hn]

theorem right_unit (m : ℕ) (x : Cell C n)
    (h : face true m x = face false m (face true m x)) :
    comp m x (face true m x) h = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    by_cases hm : m < n
    · have hc := ((C.bounded n).face_face_same false true m x).symm
      exact (comp_mk m x ((C.bounded n).face true m x) hc h).trans
        (congrArg mk ((C.bounded n).right_unit m x hc))
    · exact comp_of_le (by omega) _ _ _

theorem assoc (m : ℕ) (x y z : Cell C n)
    (hxy : face true m x = face false m y)
    (hyz : face true m y = face false m z)
    (hl : face true m (comp m x y hxy) = face false m z)
    (hr : face true m x = face false m (comp m y z hyz)) :
    comp m (comp m x y hxy) z hl = comp m x (comp m y z hyz) hr := by
  by_cases hm : m < n
  · induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        induction z using Quotient.inductionOn with
        | h z =>
          let b := C.bounded n
          have hx := matching_of_quotient hm x y hxy
          have hy := matching_of_quotient hm y z hyz
          have exy := comp_mk m x y hx hxy
          have eyz := comp_mk m y z hy hyz
          have hbl : b.target m (b.comp m x y hx) = b.source m z :=
            matching_of_quotient hm _ z (by simpa only [exy] using hl)
          have hbr : b.target m x = b.source m (b.comp m y z hy) :=
            matching_of_quotient hm x _ (by simpa only [eyz] using hr)
          calc
            _ = comp m (mk (b.comp m x y hx)) (mk z) (congrArg mk hbl) :=
              comp_congr m exy rfl hl _
            _ = mk (b.comp m (b.comp m x y hx) z hbl) := comp_mk m _ _ hbl _
            _ = mk (b.comp m x (b.comp m y z hy) hbr) :=
              congrArg mk (b.assoc m x y z hx hy hbl hbr)
            _ = comp m (mk x) (mk (b.comp m y z hy)) (congrArg mk hbr) :=
              (comp_mk m _ _ hbr _).symm
            _ = _ := comp_congr m rfl eyz.symm _ hr
  · simp only [comp_of_le (show n ≤ m by omega)]

theorem face_comp (a : Bool) (k m : ℕ) (hmk : m < k) (x y : Cell C n)
    (h : face true m x = face false m y)
    (h' : face true m (face a k x) = face false m (face a k y)) :
    face a k (comp m x y h) = comp m (face a k x) (face a k y) h' := by
  by_cases hm : m < n
  · induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        let b := C.bounded n
        have hc := matching_of_quotient hm x y h
        have hc' := matching_of_quotient hm (b.face a k x) (b.face a k y) h'
        exact (congrArg (face a k) (comp_mk m x y hc h)).trans
          ((congrArg mk (b.face_comp a k m hmk x y hc hc')).trans
            (comp_mk m (b.face a k x) (b.face a k y) hc' h').symm)
  · have hn : n ≤ m := by omega
    simp only [comp_of_le hn]

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

section

/-! # The strict category underlying intelligent truncation -/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

variable {C : StrictOmegaCategory.{0}} {n : ℕ}

theorem interchange (k m : ℕ) (hkm : k < m) (a b c d : Cell C n)
    (hab : face true k a = face false k b) (hcd : face true k c = face false k d)
    (hac : face true m a = face false m c) (hbd : face true m b = face false m d)
    (hl : face true m (comp k a b hab) = face false m (comp k c d hcd))
    (hr : face true k (comp m a c hac) = face false k (comp m b d hbd)) :
    comp m (comp k a b hab) (comp k c d hcd) hl =
      comp k (comp m a c hac) (comp m b d hbd) hr := by
  by_cases hm : m < n
  · have hk : k < n := by omega
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        induction c using Quotient.inductionOn with
        | h c =>
          induction d using Quotient.inductionOn with
          | h d =>
            let B := C.bounded n
            have ab := matching_of_quotient hk a b hab
            have cd := matching_of_quotient hk c d hcd
            have ac := matching_of_quotient hm a c hac
            have bd := matching_of_quotient hm b d hbd
            have eab := comp_mk k a b ab hab
            have ecd := comp_mk k c d cd hcd
            have eac := comp_mk m a c ac hac
            have ebd := comp_mk m b d bd hbd
            have hL : B.target m (B.comp k a b ab) = B.source m (B.comp k c d cd) :=
              matching_of_quotient hm _ _ (by simpa only [eab, ecd] using hl)
            have hR : B.target k (B.comp m a c ac) = B.source k (B.comp m b d bd) :=
              matching_of_quotient hk _ _ (by simpa only [eac, ebd] using hr)
            calc
              _ = comp m (mk (B.comp k a b ab)) (mk (B.comp k c d cd)) (congrArg mk hL) :=
                comp_congr m eab ecd hl _
              _ = mk (B.comp m (B.comp k a b ab) (B.comp k c d cd) hL) :=
                comp_mk m _ _ hL _
              _ = mk (B.comp k (B.comp m a c ac) (B.comp m b d bd) hR) :=
                congrArg mk (B.interchange k m hkm a b c d ab cd ac bd hL hR)
              _ = comp k (mk (B.comp m a c ac)) (mk (B.comp m b d bd)) (congrArg mk hR) :=
                (comp_mk k _ _ hR _).symm
              _ = _ := comp_congr k eac.symm ebd.symm _ hr
  · simp only [comp_of_le (show n ≤ m by omega)]

noncomputable def category (C : StrictOmegaCategory.{0}) (n : ℕ) : StrictOmegaCategory.{0} where
  Cell := Cell C n
  face := face
  globular := globular
  comp := comp
  source_comp := source_comp
  target_comp := target_comp
  face_comp := face_comp
  left_unit := left_unit
  right_unit := right_unit
  assoc := assoc
  interchange := interchange
  finite_dimension x := ⟨n, face_of_le (Nat.le_refl n) false x, face_of_le (Nat.le_refl n) true x⟩

theorem isTruncated (C : StrictOmegaCategory.{0}) (n : ℕ) : (category C n).IsTruncated n :=
  fun x => ⟨face_of_le (Nat.le_refl n) false x, face_of_le (Nat.le_refl n) true x⟩

/-- The quotient projection from the bounded representative category. -/
noncomputable def projection (C : StrictOmegaCategory.{0}) (n : ℕ) :
    (C.bounded n).Hom (category C n) where
  toFun := mk
  map_face _ _ _ := rfl
  map_comp m x y h h' := (comp_mk m x y h h').symm

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

section

/-! # The canonical strict functor to intelligent truncation -/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

open CategoryTheory

variable {C : StrictOmegaCategory.{0}} {n : ℕ}

def unitCell (x : C) : Cell C n := mk (topFace C n false x)

theorem unitCell_face (a : Bool) (m : ℕ) (x : C) :
    unitCell (n := n) (C.face a m x) = face a m (unitCell (n := n) x) := by
  by_cases hmn : m < n
  · change mk (topFace C n false (C.face a m x)) =
      mk ((C.bounded n).face a m (topFace C n false x))
    apply congrArg mk
    apply Subtype.ext
    change C.face false n (C.face a m x) = C.face a m (C.face false n x)
    simp only [C.globular, hmn, show ¬n < m by omega, ite_false, ite_true]
  · rw [face_of_le (show n ≤ m by omega)]
    by_cases hnm : n < m
    · apply congrArg mk
      apply Subtype.ext
      exact (C.globular false a n m x).trans (ite_eq_left hnm)
    · have he : m = n := by omega
      subst m
      change mk (topFace C n false (C.face a n x)) = mk (topFace C n false x)
      have hx : topFace C n false (C.face a n x) = topFace C n a x :=
        Subtype.ext (C.face_face_same false a n x)
      rw [hx]
      cases a
      · rfl
      · exact Quotient.sound (Rel.symm (Rel.collapse x))

theorem unitCell_comp (m : ℕ) (x y : C) (h : C.target m x = C.source m y)
    (h' : face true m (unitCell (n := n) x) = face false m (unitCell (n := n) y)) :
    unitCell (n := n) (C.comp m x y h) = comp m (unitCell x) (unitCell y) h' := by
  by_cases hmn : m < n
  · have hc : (C.bounded n).target m (topFace C n false x) =
        (C.bounded n).source m (topFace C n false y) := by
      apply Subtype.ext
      change C.face true m (C.face false n x) = C.face false m (C.face false n y)
      simpa only [C.globular, hmn, ite_true] using h
    change mk (topFace C n false (C.comp m x y h)) =
      comp m (mk (topFace C n false x)) (mk (topFace C n false y)) h'
    rw [comp_mk m _ _ hc h']
    apply congrArg mk
    apply Subtype.ext
    exact C.face_comp false n m hmn x y h (congrArg Subtype.val hc)
  · rw [comp_of_le (show n ≤ m by omega)]
    apply congrArg mk
    apply Subtype.ext
    change C.face false n (C.comp m x y h) = C.face false n x
    by_cases hlt : n < m
    · exact C.lower_face_comp false hlt x y h
    · have he : m = n := by omega
      subst m
      exact C.source_comp n x y h

/-- Kill all cells above n by their source, imposing the necessary n-cell relation. -/
noncomputable def unit (C : StrictOmegaCategory.{0}) (n : ℕ) : C ⟶ category C n where
  toFun := unitCell
  map_face := unitCell_face
  map_comp := unitCell_comp

/-- Every quotient cell is represented by an original cell of dimension at most n. -/
theorem unit_surjective (C : StrictOmegaCategory.{0}) (n : ℕ) :
    Function.Surjective (unit C n).toFun := by
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    refine ⟨x.val, ?_⟩
    apply congrArg mk
    exact Subtype.ext x.property.1

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

section

/-! # Universal descent into a strict finite-dimensional category -/

namespace Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

open CategoryTheory

variable {C D : StrictOmegaCategory.{0}} {n : ℕ}

def descendCell (hD : D.IsTruncated n) (f : C ⟶ D) (x : Cell C n) : D :=
  Quotient.liftOn x (fun z => f.toFun z.val) (fun _ _ h => h.map_eq hD f)

@[simp] theorem descendCell_mk (hD : D.IsTruncated n) (f : C ⟶ D) (x : C.bounded n) :
    descendCell hD f (mk x) = f.toFun x.val := rfl

noncomputable def descend (hD : D.IsTruncated n) (f : C ⟶ D) : category C n ⟶ D where
  toFun := descendCell hD f
  map_face a m x := by
    induction x using Quotient.inductionOn with
    | h x => exact f.map_face a m x.val
  map_comp m x y h h' := by
    change Cell C n at x y
    change face true m x = face false m y at h
    change descendCell hD f (comp m x y h) = D.comp m (descendCell hD f x) (descendCell hD f y) h'
    by_cases hm : m < n
    · induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y =>
          have hc := matching_of_quotient hm x y h
          rw [comp_mk m x y hc h]
          exact f.map_comp m x.val y.val (congrArg Subtype.val hc) h'
    · rw [comp_of_le (show n ≤ m by omega)]
      have hx := D.dimensionLE_mono (show n ≤ m by omega) (hD (descendCell hD f x))
      have hy := D.dimensionLE_mono (show n ≤ m by omega) (hD (descendCell hD f y))
      have he : descendCell hD f x = descendCell hD f y := hx.2.symm.trans (h'.trans hy.1)
      exact he.trans (D.comp_of_dimensionLE (show n ≤ m by omega)
        (hD (descendCell hD f x)) h').symm

/-- The descended functor agrees with the given functor on every original cell. -/
theorem unit_descend (hD : D.IsTruncated n) (f : C ⟶ D) :
    unit C n ≫ descend hD f = f := by
  apply Hom.ext
  funext x
  change f.toFun (C.face false n x) = f.toFun x
  exact (f.map_face false n x).trans (hD (f.toFun x)).1

/-- Uniqueness is cellwise surjectivity of the explicit quotient unit. -/
theorem unit_hom_ext {g g' : category C n ⟶ D}
    (h : unit C n ≫ g = unit C n ≫ g') : g = g' := by
  apply Hom.ext
  funext x
  obtain ⟨z, rfl⟩ := unit_surjective C n x
  exact congrArg (fun k : C ⟶ D => k.toFun z) h

theorem descend_unique (hD : D.IsTruncated n) (f : C ⟶ D)
    (g : category C n ⟶ D) (hg : unit C n ≫ g = f) : g = descend hD f :=
  unit_hom_ext (hg.trans (unit_descend hD f).symm)

end Thomason.Construction.StrictOmegaCategory.IntelligentTruncation

end

section

/-! # Exact inverse images of vertex stars under simplicial maps -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- A target vertex has positive mass precisely when some source vertex
    over it has positive mass. Repeated vertices are allowed. -/
theorem map_mem_vertexStar_iff {K L : SSet.{0}} (f : K ⟶ L)
    (x : SSet.toTop.obj K) (w : L.obj (.op (.mk 0))) :
    (SSet.toTop.map f).hom x ∈ vertexStar L w ↔
      ∃ v, f.app (.op (.mk 0)) v = w ∧ x ∈ vertexStar K v := by
  classical
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  rw [simplexPoint_naturality, simplexPoint_mem_vertexStar_iff]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨simplexVertex K s i, ?_, ?_⟩
    · rwa [simplexVertex_naturality] at he
    · exact (simplexPoint_mem_vertexStar_iff K s p _).mpr ⟨i, hi, rfl⟩
  · rintro ⟨v, hv, hx⟩
    obtain ⟨i, hi, he⟩ := (simplexPoint_mem_vertexStar_iff K s p v).mp hx
    exact ⟨i, hi, by rw [simplexVertex_naturality, he, hv]⟩

/-- A relation between maps on vertices transports positive vertex support
    for every point of the actual realization. -/
theorem vertexStar_transfer {K L M : SSet.{0}} (f : K ⟶ L) (g : K ⟶ M)
    (v : L.obj (.op (.mk 0))) (w : M.obj (.op (.mk 0)))
    (h : ∀ u, f.app (.op (.mk 0)) u = v → g.app (.op (.mk 0)) u = w)
    (x : SSet.toTop.obj K) (hx : (SSet.toTop.map f).hom x ∈ vertexStar L v) :
    (SSet.toTop.map g).hom x ∈ vertexStar M w := by
  obtain ⟨u, hu, hx⟩ := (map_mem_vertexStar_iff f x v).mp hx
  exact (map_mem_vertexStar_iff g x w).mpr ⟨u, h u hu, hx⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Full subposets as actual closed subspaces of realizations -/

namespace Thomason.Construction

open CategoryTheory Opposite RealizationPrism Topology
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

instance fullSubposetInclusion_nerve_mono (A : Set P) :
    Mono (nerveMap (fullSubposetInclusion A)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro s t h
  apply nerve.ext_of_isThin
  funext i
  apply Subtype.ext
  exact congrArg (fun u : (nerve P).obj n => u.obj i) h

def fullSubposetIso (A : Set P) : nerve A ≅ (fullSubposetComplex A : SSet) :=
  asIso (SSet.Subcomplex.toRange (nerveMap (fullSubposetInclusion A))) ≪≫
    (SSet.Subcomplex.eqToIso (fullSubposetComplex_eq_range A)).symm

theorem fullSubposetIso_hom_ι (A : Set P) :
    (fullSubposetIso A).hom ≫ (fullSubposetComplex A).ι =
      nerveMap (fullSubposetInclusion A) := by
  simp [fullSubposetIso]

def fullSubposetCarrierHomeomorph (A : Set P) :
    SSet.toTop.obj (nerve A) ≃ₜ
      Set.ofPred (fun x : SSet.toTop.obj (nerve P) =>
        carrier (nerve P) x ≤ fullSubposetComplex A) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (fullSubposetIso A))).trans
    (carrierHomeomorph (nerve P) (fullSubposetComplex A))

theorem fullSubposetCarrierHomeomorph_inclusion (A : Set P)
    (x : SSet.toTop.obj (nerve A)) :
    (fullSubposetCarrierHomeomorph A x).val =
      (SSet.toTop.map (nerveMap (fullSubposetInclusion A))).hom x := by
  have he := congrArg SSet.toTop.map (fullSubposetIso_hom_ι A)
  rw [SSet.toTop.map_comp] at he
  exact congrArg (fun f => f.hom x) he

/-- Full induced subposets realize as actual closed embeddings. -/
theorem fullSubposet_realization_isClosedEmbedding (A : Set P) :
    IsClosedEmbedding (SSet.toTop.map (nerveMap (fullSubposetInclusion A))).hom := by
  have he : (SSet.toTop.map (nerveMap (fullSubposetInclusion A))).hom =
      (carrierInclusion (nerve P) (fullSubposetComplex A)).comp
        (fullSubposetCarrierHomeomorph A : C(_, _)) := by
    ext x
    exact (fullSubposetCarrierHomeomorph_inclusion A x).symm
  rw [he]
  exact (carrier_isClosed (nerve P) (fullSubposetComplex A)).isClosedEmbedding_subtypeVal.comp
    (fullSubposetCarrierHomeomorph A).isClosedEmbedding

end

end Thomason.Construction

end

section

/-! # The carrier of a poset vertex star lies in the comparable subposet -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Opposite Convexity RealizationPrism NormalizedSimplexIdentities
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

def vertex (v : P) : (nerve P).obj (.op (.mk 0)) :=
  orderSimplex (OrderHom.const (Fin 1) v)

theorem simplexVertex_obj {n : ℕ} (s : (nerve P).obj (.op (.mk n))) (i : Fin (n+1)) :
    (simplexVertex (nerve P) s i).obj 0 = s.obj i := rfl

theorem vertex_injective : Function.Injective (vertex (P := P)) := by
  intro v w h
  exact congrArg (fun s => s.obj 0) h

def comparable (v : P) : Set P := Set.ofPred (fun x => x ≤ v ∨ v ≤ x)

/-- Every positive-support vertex in a simplex containing `v` is comparable
    with `v`; passing to the intrinsic interior removes zero-weight vertices. -/
theorem vertexStar_carrier (v : P) (x : SSet.toTop.obj (nerve P))
    (hx : x ∈ vertexStar (nerve P) (vertex v)) :
    carrier (nerve P) x ≤ fullSubposetComplex (comparable v) := by
  let s := (normalization (nerve P) x).1
  let p := (normalization (nerve P) x).2
  have hp : p ∈ fullSupport s.dim := normalization_fullSupport (nerve P) x
  have he : simplexPoint (nerve P) s.simplex p = x := denormalize_normalization (nerve P) x
  rw [← he, carrier_interior (nerve P) s.simplex p hp, SSet.Subcomplex.ofSimplex_le_iff]
  rw [← he] at hx
  obtain ⟨i, _, hi⟩ := (simplexPoint_mem_vertexStar_iff (nerve P) s.simplex p (vertex v)).mp hx
  have hi' : s.simplex.obj i = v := congrArg (fun z => z.obj 0) hi
  intro j
  change s.simplex.obj j ≤ v ∨ v ≤ s.simplex.obj j
  rcases le_total j i with hji | hij
  · left
    rw [← hi']
    exact leOfHom (s.simplex.map (homOfLE hji))
  · right
    rw [← hi']
    exact leOfHom (s.simplex.map (homOfLE hij))

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Intrinsic barycentric coordinates for poset realizations -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Opposite Convexity RealizationPrism
open scoped Simplicial

noncomputable section

variable (P : Type) [PartialOrder P]

/-- Combine the zero-simplex coordinates using the corresponding poset elements. -/
def coordinates : C(SSet.toTop.obj (nerve P), StdSimplex ℝ P) :=
  (⟨StdSimplex.map (fun v : (nerve P).obj (.op (.mk 0)) => v.obj 0),
    StdSimplex.continuous_map ℝ _⟩ : C(_, _)).comp (vertexCoordinates (nerve P))

theorem coordinates_simplexPoint {n : ℕ} (s : (nerve P).obj (.op (.mk n)))
    (p : StdSimplex ℝ (Fin (n+1))) :
    coordinates P (simplexPoint (nerve P) s p) = StdSimplex.map s.obj p := by
  change StdSimplex.map (fun v : (nerve P).obj (.op (.mk 0)) => v.obj 0)
    (vertexCoordinates (nerve P) (simplexPoint (nerve P) s p)) = _
  rw [vertexCoordinates_simplexPoint]
  change StdSimplex.map (fun v : (nerve P).obj (.op (.mk 0)) => v.obj 0)
    (StdSimplex.map (simplexVertex (nerve P) s) p) = _
  rw [← StdSimplex.map_comp]
  rfl

/-- For an interior point, positive barycentric support is exactly the
    set of vertices of its intrinsic simplex. -/
theorem coordinates_support_interior {n : ℕ} (s : (nerve P).obj (.op (.mk n)))
    (p : StdSimplex ℝ (Fin (n+1))) (hp : p ∈ fullSupport n) (v : P) :
    v ∈ (coordinates P (simplexPoint (nerve P) s p)).weights.support ↔
      v ∈ Set.range s.obj := by
  classical
  rw [coordinates_simplexPoint]
  change v ∈ (Finsupp.mapDomain s.obj p.weights).support ↔ _
  rw [Finsupp.support_mapDomain_of_nonneg p.nonneg]
  simp only [Finset.mem_image, Finsupp.mem_support_iff, Set.mem_range]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hp i, hi⟩

/-- Equal coordinates of nondegenerate interior points give equal actual
    realization points, including all possible face identifications. -/
theorem interior_eq_of_coordinates_eq (s t : (nerve P).N)
    (p : StdSimplex ℝ (Fin (s.dim+1))) (q : StdSimplex ℝ (Fin (t.dim+1)))
    (hp : p ∈ fullSupport s.dim) (hq : q ∈ fullSupport t.dim)
    (he : coordinates P (simplexPoint (nerve P) s.simplex p) =
      coordinates P (simplexPoint (nerve P) t.simplex q)) :
    simplexPoint (nerve P) s.simplex p = simplexPoint (nerve P) t.simplex q := by
  have hr : Set.range s.simplex.obj = Set.range t.simplex.obj := by
    ext v
    rw [← coordinates_support_interior P s.simplex p hp,
      ← coordinates_support_interior P t.simplex q hq, he]
  have hs : s = t := by
    apply SSet.N.subcomplex_injective
    apply le_antisymm
    · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff _ _).mpr hr.le
    · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff _ _).mpr hr.ge
  subst t
  rw [coordinates_simplexPoint, coordinates_simplexPoint] at he
  have hi : Function.Injective s.simplex.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_injective _).mp s.nonDegenerate
  have hpq : p = q := by
    apply StdSimplex.ext
    exact Finsupp.mapDomain_injective hi (congrArg StdSimplex.weights he)
  rw [hpq]

/-- Barycentric vertex coordinates distinguish every point of the actual
    realization of a poset nerve, without a finiteness assumption. -/
theorem coordinates_injective : Function.Injective (coordinates P) := by
  intro x y he
  let s := (normalization (nerve P) x).1
  let t := (normalization (nerve P) y).1
  let p := (normalization (nerve P) x).2
  let q := (normalization (nerve P) y).2
  have hx : simplexPoint (nerve P) s.simplex p = x := denormalize_normalization _ x
  have hy : simplexPoint (nerve P) t.simplex q = y := denormalize_normalization _ y
  rw [← hx, ← hy] at he ⊢
  exact interior_eq_of_coordinates_eq P s t p q
    (normalization_fullSupport _ x) (normalization_fullSupport _ y) he

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Finite poset realizations as embedded barycentric spaces -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism Topology
open scoped Simplicial

noncomputable section

variable (P : Type) [PartialOrder P]

/-- A nondegenerate poset simplex is determined by its finite vertex set. -/
def vertexSet (s : (nerve P).N) : Finset P := by
  classical
  exact Finset.univ.image s.simplex.obj

theorem vertexSet_injective : Function.Injective (vertexSet P) := by
  classical
  intro s t h
  have hr : Set.range s.simplex.obj = Set.range t.simplex.obj := by
    simpa only [vertexSet, Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      congrArg (fun u : Finset P => (u : Set P)) h
  apply SSet.N.subcomplex_injective
  apply le_antisymm
  · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff _ _).mpr hr.le
  · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff _ _).mpr hr.ge

/-- Finitely many vertices in a poset give finitely many nondegenerate
    nerve simplices, rather than merely degreewise finiteness. -/
theorem nerve_finite [Finite P] : (nerve P).Finite where
  finite := Finite.of_injective (vertexSet P) (vertexSet_injective P)

/-- For finite posets the coordinate injection is a closed embedding. -/
theorem coordinates_isClosedEmbedding [Finite P] : IsClosedEmbedding (coordinates P) := by
  let : (nerve P).Finite := nerve_finite P
  let : CompactSpace (SSet.toTop.obj (nerve P)) := compactSpace_of_finite _
  let : T2Space (StdSimplex ℝ P) := (StdSimplex.isEmbedding_toFun_comp_weights ℝ P).t2Space
  exact .of_continuous_injective_isClosedMap (coordinates P).continuous
    (coordinates_injective P) (coordinates P).continuous.isClosedMap

/-- The actual finite-poset realization is homeomorphic to its barycentric image. -/
def coordinatesHomeomorph [Finite P] :
    SSet.toTop.obj (nerve P) ≃ₜ Set.range (coordinates P) :=
  (coordinates_isClosedEmbedding P).isEmbedding.toHomeomorph

end

end Thomason.Construction.PosetGeometry

end

end OAI
