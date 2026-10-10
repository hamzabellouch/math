import Mathlib
import OAI.CategoryTheory.Thomason.StandardComparison

namespace OAI

/-! Cylinder Profiles. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}}

lemma generatorCylinder_endpoint (n : ℕ) (x : X.Cells n) (a : Bool)
    (t : Table (complex.{u} n)) :
    (generatorCylinder n x).map (atEnd a t) =
      ((tensorEndpoint a).app X).map ((GlobeComplex.lift x.val x.property).map t) := by
  have h : OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu (generatorCylinder n x) =
      OmegaCategory.Functor.comp (GlobeComplex.lift x.val x.property) ((tensorEndpoint a).app X) := by
    apply GlobeComplex.functor_ext
    change (tensorPresentation X).generator ⟨n,x,atEnd a (topTable n)⟩ =
      ((tensorEndpoint a).app X).map ((GlobeComplex.lift x.val x.property).map (topTable n))
    rw [lift_top,tensorEndpoint_bounded a X n x]
  exact congrArg (fun F => F.map t) h

def tensorParameter (X : OmegaCategory.{u}) : tensorFunctor.obj X ⟶ (K.{u} 0).nu :=
  tensorFunctor.map (constantAt X (topTable 0) (topTable_bounded 0)) ≫ (globeTensorIso 0).hom

def tensorLabel (t : (tensorFunctor.obj X).Cell) (b : Bool) : ℤ :=
  intervalLabel ((tensorParameter X).map t) b

lemma tensorParameter_generator (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) :
    (tensorParameter X).map ((tensorPresentation X).generator ⟨n,x,z⟩) =
      (faceMap.{u} 0 n false).cylinder.nu.map z := by
  change (globeTensorHom 0).map ((tensorFunctor.map (constantAt X (topTable 0) (topTable_bounded 0))).map
    ((tensorPresentation X).generator ⟨n,x,z⟩)) = _
  erw [tensorFunctor_map_generator,globeTensorHom_generator]
  change (eval n ((globeDiagram 0).map (topTable 0))).map z = _
  rw [globeDiagram_top,eval_ofMap]
  rfl

lemma intervalLabel_cylinder_map {n m : ℕ} (f : Hom (complex.{u} n) (complex.{u} m))
    (z : Table (K.{u} n)) (b : Bool) :
    intervalLabel (f.cylinder.nu.map z) b = intervalLabel z b :=
  f.map_augmentation ((z.row 0 b).2)

@[simp] lemma tensorLabel_generator (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) (b : Bool) :
    tensorLabel ((tensorPresentation X).generator ⟨n,x,z⟩) b = intervalLabel z b := by
  unfold tensorLabel
  rw [tensorParameter_generator,intervalLabel_cylinder_map]

@[simp] lemma tensorLabel_endpoint (a b : Bool) (x : X.Cell) :
    tensorLabel (((tensorEndpoint a).app X).map x) b = if a then 1 else 0 := by
  obtain ⟨n,hn⟩ := X.finite_dimension x
  erw [tensorEndpoint_bounded a X n ⟨x,hn⟩,tensorLabel_generator,intervalLabel_end]

lemma tensorLabel_values (x : (tensorFunctor.obj X).Cell) (b : Bool) :
    tensorLabel x b = 0 ∨ tensorLabel x b = 1 :=
  side_mass_vertex ((tensorParameter X).map x) true b

lemma tensorLabel_monotone (x : (tensorFunctor.obj X).Cell) :
    tensorLabel x false ≤ tensorLabel x true := interval_monotone ((tensorParameter X).map x)

lemma tensorLabel_source (k : ℕ) (x : (tensorFunctor.obj X).Cell) (b : Bool) :
    tensorLabel ((tensorFunctor.obj X).source k x) b =
      if k = 0 then tensorLabel x false else tensorLabel x b := by
  unfold tensorLabel
  rw [(tensorParameter X).map_source]
  cases k with
  | zero => rfl
  | succ k => rfl

lemma tensorLabel_target (k : ℕ) (x : (tensorFunctor.obj X).Cell) (b : Bool) :
    tensorLabel ((tensorFunctor.obj X).target k x) b =
      if k = 0 then tensorLabel x true else tensorLabel x b := by
  unfold tensorLabel
  rw [(tensorParameter X).map_target]
  cases k with
  | zero => rfl
  | succ k => rfl

lemma tensorLabel_comp (k : ℕ) (x y : (tensorFunctor.obj X).Cell)
    (h : (tensorFunctor.obj X).target k x = (tensorFunctor.obj X).source k y) :
    tensorLabel ((tensorFunctor.obj X).comp k x y h) false = tensorLabel x false ∧
      tensorLabel ((tensorFunctor.obj X).comp k x y h) true = tensorLabel y true := by
  have hs := congrArg (fun z => tensorLabel z false)
    ((tensorFunctor.obj X).source_comp_le 0 k (Nat.zero_le _) x y h)
  have ht := congrArg (fun z => tensorLabel z true)
    ((tensorFunctor.obj X).target_comp_le 0 k (Nat.zero_le _) x y h)
  simpa only [tensorLabel_source,tensorLabel_target,ite_self] using And.intro hs ht

lemma tensorLabel_comp_stationary (k : ℕ) (x y : (tensorFunctor.obj X).Cell)
    (h : (tensorFunctor.obj X).target k x = (tensorFunctor.obj X).source k y) (a : ℤ)
    (hs : tensorLabel ((tensorFunctor.obj X).comp k x y h) false = a)
    (ht : tensorLabel ((tensorFunctor.obj X).comp k x y h) true = a) :
    (∀ b, tensorLabel x b = a) ∧ ∀ b, tensorLabel y b = a := by
  obtain ⟨h₀,h₁⟩ := tensorLabel_comp k x y h
  have hx : tensorLabel x false = a := h₀.symm.trans hs
  have hy : tensorLabel y true = a := h₁.symm.trans ht
  have hm (b : Bool) := congrArg (fun z => tensorLabel z b) h
  simp only [tensorLabel_source,tensorLabel_target] at hm
  have hx' : tensorLabel x true = a := by
    by_cases hk : k = 0
    · have hm' := hm false
      rw [ite_eq_left hk,ite_eq_left hk] at hm'
      have hxle := tensorLabel_monotone x
      have hyle := tensorLabel_monotone y
      omega
    · have hm' := hm true
      simpa only [ite_eq_right hk,hy] using hm'
  have hy' : tensorLabel y false = a := by
    by_cases hk : k = 0
    · have hm' := hm false
      rw [ite_eq_left hk,ite_eq_left hk,hx'] at hm'
      exact hm'.symm
    · have hm' := hm false
      simpa only [ite_eq_right hk,hx] using hm'.symm
  constructor <;> intro b <;> cases b
  · exact hx
  · exact hx'
  · exact hy'
  · exact hy

lemma tensor_zero_faces_are_endpoints (z : (tensorFunctor.obj X).Cell) :
    (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 z = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 z = ((tensorEndpoint a).app X).map x := by
  apply (tensorPresentation X).cells_induction (fun z =>
    (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 z = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 z = ((tensorEndpoint a).app X).map x)
  · rintro ⟨n,x,t⟩
    have hh (b : Bool) : ∃ (a : Bool) (q : X.Cell),
        (tensorFunctor.obj X).face 0 b ((tensorPresentation X).generator ⟨n,x,t⟩) =
          ((tensorEndpoint a).app X).map q := by
      obtain ⟨a,ha⟩ := endpoint_of_stationary_interval (truncate 0 b t) (by rfl)
      refine ⟨a,(GlobeComplex.lift x.val x.property).map (project (truncate 0 b t)),?_⟩
      change (tensorPresentation X).category.face 0 b ((generatorCylinder n x).map t) = _
      rw [← (generatorCylinder n x).map_face]
      have hf : (K n).nu.face 0 b t = truncate 0 b t := by cases b <;> rfl
      rw [hf]
      conv_lhs => rw [ha]
      exact generatorCylinder_endpoint n x a _
    exact ⟨hh false,hh true⟩
  · intro k z hz
    change (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).source k z) = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).source k z) = ((tensorEndpoint a).app X).map x
    constructor
    · erw [(tensorFunctor.obj X).source_source,Nat.min_eq_left (Nat.zero_le _)]
      exact hz.1
    · cases k with
      | zero =>
        erw [(tensorFunctor.obj X).target_source_self]
        exact hz.1
      | succ k =>
        erw [(tensorFunctor.obj X).target_source]
        simpa only [Nat.zero_lt_succ,ite_true] using hz.2
  · intro k z hz
    change (∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).target k z) = ((tensorEndpoint a).app X).map x) ∧
      ∃ (a : Bool) (x : X.Cell), (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).target k z) = ((tensorEndpoint a).app X).map x
    constructor
    · cases k with
      | zero =>
        erw [(tensorFunctor.obj X).source_target_self]
        exact hz.2
      | succ k =>
        erw [(tensorFunctor.obj X).source_target]
        simpa only [Nat.zero_lt_succ,ite_true] using hz.1
    · erw [(tensorFunctor.obj X).target_target,Nat.min_eq_left (Nat.zero_le _)]
      exact hz.2
  · intro k x y h hx hy
    change (∃ (a : Bool) (t : X.Cell), (tensorFunctor.obj X).source 0 ((tensorFunctor.obj X).comp k x y h) = ((tensorEndpoint a).app X).map t) ∧
      ∃ (a : Bool) (t : X.Cell), (tensorFunctor.obj X).target 0 ((tensorFunctor.obj X).comp k x y h) = ((tensorEndpoint a).app X).map t
    constructor
    · erw [(tensorFunctor.obj X).source_comp_le 0 k (Nat.zero_le _)]
      exact hx.1
    · erw [(tensorFunctor.obj X).target_comp_le 0 k (Nat.zero_le _)]
      exact hy.2

lemma tensorEndpoint_injective (a : Bool) :
    Function.Injective (((tensorEndpoint a).app X).map) := by
  intro x y h
  have hp (t : X.Cell) : (tensorProjection.app X).map (((tensorEndpoint a).app X).map t) = t :=
    congrArg (fun F : X ⟶ X => F.map t) (congrArg (fun η => η.app X) (tensorEndpoint_projection a))
  have hh := congrArg (tensorProjection.app X).map h
  simpa only [hp] using hh

lemma tensorEndpoint_eq_iff (a b : Bool) (x y : X.Cell) :
    ((tensorEndpoint a).app X).map x = ((tensorEndpoint b).app X).map y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z => tensorLabel z false) h
    rw [tensorLabel_endpoint,tensorLabel_endpoint] at hh
    have hab : a = b := by cases a <;> cases b <;> first | rfl | norm_num at hh
    subst b
    exact ⟨rfl,tensorEndpoint_injective a h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma tensor_object_endpoint (z : (tensorFunctor.obj X).Cell)
    (hz : (tensorFunctor.obj X).source 0 z = z) :
    ∃! ax : Bool × X.Objects, z = ((tensorEndpoint ax.1).app X).map ax.2.val := by
  obtain ⟨a,x,hx⟩ := (tensor_zero_faces_are_endpoints z).1
  have he : z = ((tensorEndpoint a).app X).map x := hz.symm.trans hx
  have hxb : X.source 0 x = x := by
    apply tensorEndpoint_injective a
    change ((tensorEndpoint a).app X).map (((𝟭 OmegaCategory).obj X).source 0 x) = _
    rw [((tensorEndpoint a).app X).map_source,← he,hz]
  refine ⟨⟨a,⟨x,hxb⟩⟩,he,?_⟩
  rintro ⟨b,y⟩ hy
  have hh := (tensorEndpoint_eq_iff b a y.val x).mp (hy.symm.trans he)
  exact Prod.ext hh.1 (Subtype.ext hh.2)

lemma tensor_object_reconstruct (z : (tensorFunctor.obj X).Cell)
    (hz : (tensorFunctor.obj X).source 0 z = z) (a : Bool)
    (ha : tensorLabel z false = if a then 1 else 0) :
    z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z) := by
  obtain ⟨⟨b,x⟩,hx,_⟩ := tensor_object_endpoint z hz
  have he := ha
  rw [hx,tensorLabel_endpoint] at he
  have hab : a = b := by cases a <;> cases b <;> first | rfl | norm_num at he
  subst b
  have hp := congrArg (fun F : X ⟶ X => F.map x.val)
    (congrArg (fun η => η.app X) (tensorEndpoint_projection a))
  change (tensorProjection.app X).map (((tensorEndpoint a).app X).map x.val) = x.val at hp
  rw [hx,hp]

lemma generatorCylinder_stationary (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) (a : Bool)
    (hs : intervalLabel z false = if a then 1 else 0)
    (ht : intervalLabel z true = if a then 1 else 0) :
    (tensorPresentation X).generator ⟨n,x,z⟩ =
      ((tensorEndpoint a).app X).map ((tensorProjection.app X).map
        ((tensorPresentation X).generator ⟨n,x,z⟩)) := by
  obtain ⟨b,hb⟩ := endpoint_of_stationary_interval z (ht.trans hs.symm)
  have he := hs
  change z = atEnd b (project z) at hb
  rw [hb,intervalLabel_end] at he
  have hab : a = b := by cases a <;> cases b <;> first | rfl | norm_num at he
  subst b
  erw [tensorProjection_generator X n x z]
  change (generatorCylinder n x).map z = _
  conv_lhs => rw [hb]
  exact generatorCylinder_endpoint n x a _

lemma tensor_stationary_reconstruct (z : (tensorFunctor.obj X).Cell) (a : Bool)
    (hs : tensorLabel z false = if a then 1 else 0)
    (ht : tensorLabel z true = if a then 1 else 0) :
    z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z) := by
  let Q (z : (tensorFunctor.obj X).Cell) := ∀ a : Bool,
    tensorLabel z false = (if a then 1 else 0) → tensorLabel z true = (if a then 1 else 0) →
      z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z)
  suffices hh : Q z from hh a hs ht
  apply (tensorPresentation X).cells_induction Q
  · rintro ⟨n,x,z⟩ a hs ht
    rw [tensorLabel_generator n x z false] at hs
    rw [tensorLabel_generator n x z true] at ht
    exact generatorCylinder_stationary n x z a hs ht
  · intro k x ih a hs ht
    change tensorLabel ((tensorFunctor.obj X).source k x) false = _ at hs
    change tensorLabel ((tensorFunctor.obj X).source k x) true = _ at ht
    cases k with
    | zero => exact tensor_object_reconstruct _ ((tensorFunctor.obj X).source_source_self 0 x) a hs
    | succ k =>
      erw [tensorLabel_source] at hs ht
      simp only [Nat.succ_ne_zero,ite_false] at hs ht
      have hh := congrArg ((tensorFunctor.obj X).source (k+1)) (ih a hs ht)
      erw [← ((tensorEndpoint a).app X).map_source,← (tensorProjection.app X).map_source] at hh
      exact hh
  · intro k x ih a hs ht
    change tensorLabel ((tensorFunctor.obj X).target k x) false = _ at hs
    change tensorLabel ((tensorFunctor.obj X).target k x) true = _ at ht
    cases k with
    | zero => exact tensor_object_reconstruct _ ((tensorFunctor.obj X).source_target_self 0 x) a hs
    | succ k =>
      erw [tensorLabel_target] at hs ht
      simp only [Nat.succ_ne_zero,ite_false] at hs ht
      have hh := congrArg ((tensorFunctor.obj X).target (k+1)) (ih a hs ht)
      erw [← ((tensorEndpoint a).app X).map_target,← (tensorProjection.app X).map_target] at hh
      exact hh
  · intro k x y h ihx ihy a hs ht
    obtain ⟨hx,hy⟩ := tensorLabel_comp_stationary k x y h _ hs ht
    have hxx := ihx a (hx false) (hx true)
    have hyy := ihy a (hy false) (hy true)
    let e : tensorFunctor.obj X ⟶ tensorFunctor.obj X := tensorProjection.app X ≫ (tensorEndpoint a).app X
    change (tensorFunctor.obj X).comp k x y h = e.map ((tensorFunctor.obj X).comp k x y h)
    rw [e.map_comp k x y h (e.map_composable h)]
    congr 1
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

structure PositiveAcyclic (M : DirectedComplex.{u}) : Prop where
  augmentation_nonneg : ∀ x ∈ M.positive 0, 0 ≤ M.augmentation x
  augmentation_zero : ∀ x ∈ M.positive 0, M.augmentation x = 0 → x = 0
  cycle_zero : ∀ p (x : M.Chain (p+1)), x ∈ M.positive (p+1) → M.d p x = 0 → x = 0

namespace CylinderTables
open Table
variable {M : DirectedComplex.{u}}

def side (t : Table M.cylinder) (a : Bool) : (p : ℕ) → Bool → M.Chain p
  | 0, b => if a then (t.row 0 b).2 else (t.row 0 b).1
  | p+1, b => if a then (t.row (p+1) b).2.1 else (t.row (p+1) b).1

def cross (t : Table M.cylinder) (p : ℕ) (b : Bool) : M.Chain p :=
  (t.row (p+1) b).2.2

def project (t : Table M.cylinder) : Table M := M.cylinderProjection.table t

def label (t : Table M.cylinder) (b : Bool) : ℤ := M.augmentation (side t true 0 b)

lemma project_row (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    (project t).row p b = side t false p b + side t true p b := by cases p <;> rfl

lemma side_positive (t : Table M.cylinder) (a : Bool) (p : ℕ) (b : Bool) :
    side t a p b ∈ M.positive p := by
  cases p with
  | zero => cases a; exact (t.positive 0 b).1; exact (t.positive 0 b).2
  | succ p => cases a; exact (t.positive (p+1) b).1; exact (t.positive (p+1) b).2.1

lemma cross_positive (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    cross t p b ∈ M.positive p := (t.positive (p+1) b).2.2

lemma cross_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (cross t (p+1) b) = cross t p true - cross t p false :=
  congrArg (fun x : M.cylinder.Chain (p+1) => x.2.2) (t.boundary (p+1) b)

lemma left_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t false (p+1) b) - (-1 : ℤ)^p • cross t p b =
      side t false p true - side t false p false := by
  cases p with
  | zero => simpa [side,cross,cylinderDifferential] using congrArg Prod.fst (t.boundary 0 b)
  | succ p => exact congrArg Prod.fst (t.boundary (p+1) b)

lemma right_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t true (p+1) b) + (-1 : ℤ)^p • cross t p b =
      side t true p true - side t true p false := by
  cases p with
  | zero => simpa [side,cross,cylinderDifferential] using congrArg Prod.snd (t.boundary 0 b)
  | succ p => exact congrArg (fun x : M.cylinder.Chain (p+1) => x.2.1) (t.boundary (p+1) b)

lemma augmentation_sides (t : Table M.cylinder) (b : Bool) :
    M.augmentation (side t false 0 b) + M.augmentation (side t true 0 b) = 1 :=
  t.augmentation b

lemma augmentation_cross (t : Table M.cylinder) (b : Bool) :
    M.augmentation (cross t 0 b) = label t true - label t false := by
  have h := congrArg M.augmentation (right_boundary t 0 b)
  simpa only [map_add,map_smul,pow_zero,one_smul,M.augmentation_d,zero_add,map_sub,label] using h

lemma label_truncate (k : ℕ) (e : Bool) (t : Table M.cylinder) (b : Bool) :
    label (truncate k e t) b = if k = 0 then label t e else label t b := by
  cases k with
  | zero => rfl
  | succ k => rfl

lemma label_comp (k : ℕ) (x y : Table M.cylinder)
    (h : truncate k true x = truncate k false y) :
    label (comp k x y h) false = label x false ∧
      label (comp k x y h) true = label y true := by
  have hs := congrArg (fun z : Table M.cylinder => label z false) (source_comp_le 0 k (Nat.zero_le _) x y h)
  have ht := congrArg (fun z : Table M.cylinder => label z true) (target_comp_le 0 k (Nat.zero_le _) x y h)
  simpa only [label_truncate,ite_self] using And.intro hs ht

lemma label_endpoint (a b : Bool) (x : Table M) :
    label ((M.cylinderEndpoint a).table x) b = if a then 1 else 0 := by
  cases a
  · exact M.augmentation.map_zero
  · exact x.augmentation b

lemma label_cylinder_map {N : DirectedComplex.{v}} (f : Hom M N) (x : Table M.cylinder) (b : Bool) :
    label (f.cylinder.table x) b = label x b := f.map_augmentation (side x true 0 b)

variable (hM : PositiveAcyclic M)
include hM

lemma label_values (t : Table M.cylinder) (b : Bool) :
    label t b = 0 ∨ label t b = 1 := by
  have h := augmentation_sides t b
  have h₀ := hM.augmentation_nonneg _ (side_positive t false 0 b)
  have h₁ := hM.augmentation_nonneg _ (side_positive t true 0 b)
  dsimp [label]
  omega

lemma label_monotone (t : Table M.cylinder) : label t false ≤ label t true := by
  have h := hM.augmentation_nonneg _ (cross_positive t 0 false)
  rw [augmentation_cross] at h
  omega

lemma cross_zero_of_stationary (t : Table M.cylinder) (h : label t true = label t false) :
    ∀ p b, cross t p b = 0 := by
  intro p b
  induction p generalizing b with
  | zero =>
    exact hM.augmentation_zero _ (cross_positive t 0 b) (by rw [augmentation_cross,h,sub_self])
  | succ p ih =>
    exact hM.cycle_zero p _ (cross_positive t (p+1) b) (by rw [cross_boundary,ih true,ih false,sub_self])

lemma side_zero_of_empty (t : Table M.cylinder) (a : Bool)
    (hc : ∀ p b, cross t p b = 0) (hs : ∀ b, side t a 0 b = 0) :
    ∀ p b, side t a p b = 0 := by
  intro p b
  induction p generalizing b with
  | zero => exact hs b
  | succ p ih =>
    apply hM.cycle_zero p _ (side_positive t a (p+1) b)
    cases a with
    | false => simpa only [hc,smul_zero,ih,sub_zero,sub_self] using left_boundary t p b
    | true => simpa only [hc,smul_zero,ih,add_zero,sub_self] using right_boundary t p b

lemma stationary_reconstruct (t : Table M.cylinder) (a : Bool)
    (hs : label t false = if a then 1 else 0)
    (ht : label t true = if a then 1 else 0) :
    t = (M.cylinderEndpoint a).table (project t) := by
  have hc := cross_zero_of_stationary hM t (ht.trans hs.symm)
  have he : ∀ p b, side t (!a) p b = 0 := by
    apply side_zero_of_empty hM t (!a) hc
    intro b
    apply hM.augmentation_zero _ (side_positive t (!a) 0 b)
    have hh : label t b = if a then 1 else 0 := by cases b; exact hs; exact ht
    have haug := augmentation_sides t b
    cases a <;> dsimp [label] at hh <;> simp only [Bool.not_false,Bool.not_true] at haug ⊢ <;> omega
  ext p b
  change t.row p b = M.cylinderEndpointMap a p ((project t).row p b)
  rw [project_row]
  cases a
  · have hz := he p b
    change side t true p b = 0 at hz
    rw [hz,add_zero]
    cases p with
    | zero => exact Prod.ext rfl hz
    | succ p => exact Prod.ext rfl (Prod.ext hz (hc p b))
  · have hz := he p b
    change side t false p b = 0 at hz
    rw [hz,zero_add]
    cases p with
    | zero => exact Prod.ext hz rfl
    | succ p => exact Prod.ext hz (Prod.ext rfl (hc p b))

lemma endpoint_or_crossing (t : Table M.cylinder) :
    (∃ a, t = (M.cylinderEndpoint a).table (project t)) ∨
      (label t false = 0 ∧ label t true = 1) := by
  have hs := label_values hM t false
  have ht := label_values hM t true
  have hm := label_monotone hM t
  by_cases h : label t false = label t true
  · left
    rcases hs with hs | hs
    · exact ⟨false,stationary_reconstruct hM t false hs (h.symm.trans hs)⟩
    · exact ⟨true,stationary_reconstruct hM t true hs (h.symm.trans hs)⟩
  · right
    constructor <;> omega

omit hM in
lemma crossing_augmentation (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (b : Bool) :
    M.augmentation (cross t 0 b) = 1 := by rw [augmentation_cross,hs,ht,sub_zero]

lemma crossing_starts_ends (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) :
    side t true 0 false = 0 ∧ side t false 0 true = 0 := by
  constructor
  · exact hM.augmentation_zero _ (side_positive t true 0 false) hs
  · apply hM.augmentation_zero _ (side_positive t false 0 true)
    have h := augmentation_sides t true
    change M.augmentation (side t false 0 true) + label t true = 1 at h
    omega

end CylinderTables
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex
variable (E : Type u) [PartialOrder E]

theorem complexPositiveAcyclic : PositiveAcyclic (complex E) where
  augmentation_nonneg x hx := by
    change 0 ≤ emptyCoefficient (boundary x.val)
    rw [augmentation_eq_sum x.property,← chainMass_eq_sum]
    exact chainMass_nonneg hx
  augmentation_zero x hx ha := Subtype.ext (positive_augmentation_zero x.property hx ha)
  cycle_zero p x hx hd := Subtype.ext (positive_cycle_zero_partial x.property hx (congrArg Subtype.val hd))

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {M : DirectedComplex.{u}}

lemma chainComparison_label (z : (tensorFunctor.obj M.nu).Cell) (b : Bool) :
    CylinderTables.label ((chainComparison M).map z) b = tensorLabel z b := by
  suffices h : ∀ b, CylinderTables.label ((chainComparison M).map z) b = tensorLabel z b from h b
  apply (tensorPresentation M.nu).cells_induction (fun z =>
    ∀ b, CylinderTables.label ((chainComparison M).map z) b = tensorLabel z b)
  · rintro ⟨n,x,t⟩ b
    erw [chainComparison_generator,tensorLabel_generator]
    change CylinderTables.label ((tableMap n x.val).cylinder.table t) b = intervalLabel t b
    exact CylinderTables.label_cylinder_map (tableMap n x.val) t b
  · intro k x ih b
    change CylinderTables.label ((chainComparison M).map ((tensorFunctor.obj M.nu).source k x)) b =
      tensorLabel ((tensorFunctor.obj M.nu).source k x) b
    erw [(chainComparison M).map_source,tensorLabel_source]
    change CylinderTables.label (truncate k false ((chainComparison M).map x)) b = _
    erw [CylinderTables.label_truncate,ih,ih]
  · intro k x ih b
    change CylinderTables.label ((chainComparison M).map ((tensorFunctor.obj M.nu).target k x)) b =
      tensorLabel ((tensorFunctor.obj M.nu).target k x) b
    erw [(chainComparison M).map_target,tensorLabel_target]
    change CylinderTables.label (truncate k true ((chainComparison M).map x)) b = _
    erw [CylinderTables.label_truncate,ih,ih]
  · intro k x y h ihx ihy b
    change CylinderTables.label ((chainComparison M).map ((tensorFunctor.obj M.nu).comp k x y h)) b = _
    rw [(chainComparison M).map_comp k x y h ((chainComparison M).map_composable h)]
    have ht := CylinderTables.label_comp k ((chainComparison M).map x) ((chainComparison M).map y)
      ((chainComparison M).map_composable h)
    have hs := tensorLabel_comp k x y h
    cases b
    · exact ht.1.trans ((ihx false).trans hs.1.symm)
    · exact ht.2.trans ((ihy true).trans hs.2.symm)

lemma chainComparison_project (z : (tensorFunctor.obj M.nu).Cell) :
    CylinderTables.project ((chainComparison M).map z) = (tensorProjection.app M.nu).map z :=
  congrArg (fun F : tensorFunctor.obj M.nu ⟶ M.nu => F.map z) (chainComparison_projection M)

lemma chainComparison_endpoint_apply (a : Bool) (x : Table M) :
    (chainComparison M).map (((tensorEndpoint a).app M.nu).map x) = (M.cylinderEndpoint a).table x :=
  congrArg (fun F : M.nu ⟶ M.cylinder.nu => F.map x) (chainComparison_endpoint M a)

lemma chainComparison_endpoint_fiber (z : (tensorFunctor.obj M.nu).Cell)
    (a : Bool) (x : Table M) :
    (chainComparison M).map z = (M.cylinderEndpoint a).table x ↔
      z = ((tensorEndpoint a).app M.nu).map x := by
  constructor
  · intro hz
    have hlabel (b : Bool) : tensorLabel z b = if a then 1 else 0 := by
      rw [← chainComparison_label,hz,CylinderTables.label_endpoint]
    have hp : (tensorProjection.app M.nu).map z = x := by
      rw [← chainComparison_project,hz]
      exact congrArg (fun F : M.nu ⟶ M.nu => F.map x)
        (show (M.cylinderEndpoint a).nu ≫ M.cylinderProjection.nu = 𝟙 M.nu from
          congrArg Hom.nu (M.cylinderProjection_endpoint a))
    exact (tensor_stationary_reconstruct z a (hlabel false) (hlabel true)).trans
      (congrArg ((tensorEndpoint a).app M.nu).map hp)
  · rintro rfl
    exact chainComparison_endpoint_apply a x

lemma tensor_endpoint_or_crossing {X : OmegaCategory.{u}} (z : (tensorFunctor.obj X).Cell) :
    (∃ a, z = ((tensorEndpoint a).app X).map ((tensorProjection.app X).map z)) ∨
      (tensorLabel z false = 0 ∧ tensorLabel z true = 1) := by
  have hs := tensorLabel_values z false
  have ht := tensorLabel_values z true
  have hm := tensorLabel_monotone z
  by_cases h : tensorLabel z false = tensorLabel z true
  · left
    rcases hs with hs | hs
    · exact ⟨false,tensor_stationary_reconstruct z false hs (h.symm.trans hs)⟩
    · exact ⟨true,tensor_stationary_reconstruct z true hs (h.symm.trans hs)⟩
  · right
    constructor <;> omega

lemma chainComparison_injective_of_crossing
    (hi : ∀ (x y : (tensorFunctor.obj M.nu).Cell),
      tensorLabel x false = 0 → tensorLabel x true = 1 →
      tensorLabel y false = 0 → tensorLabel y true = 1 →
      (chainComparison M).map x = (chainComparison M).map y → x = y) :
    Function.Injective (chainComparison M).map := by
  intro x y h
  rcases tensor_endpoint_or_crossing x with ⟨a,ha⟩ | hc
  · have hxe : (chainComparison M).map x =
        (M.cylinderEndpoint a).table ((tensorProjection.app M.nu).map x) :=
      (chainComparison_endpoint_fiber x a _).mpr ha
    exact ha.trans ((chainComparison_endpoint_fiber y a _).mp (h.symm.trans hxe)).symm
  · have hy (b : Bool) : tensorLabel y b = tensorLabel x b := by
      rw [← chainComparison_label,← chainComparison_label,h]
    exact hi x y hc.1 hc.2 ((hy false).trans hc.1) ((hy true).trans hc.2) h

lemma chainComparison_surjective_of_crossing (hM : PositiveAcyclic M)
    (hs : ∀ (t : Table M.cylinder), CylinderTables.label t false = 0 →
      CylinderTables.label t true = 1 → ∃ x, (chainComparison M).map x = t) :
    Function.Surjective (chainComparison M).map := by
  intro t
  rcases CylinderTables.endpoint_or_crossing hM t with ⟨a,ha⟩ | hc
  · exact ⟨((tensorEndpoint a).app M.nu).map (CylinderTables.project t),
      (chainComparison_endpoint_apply a _).trans ha.symm⟩
  · exact hs t hc.1 hc.2

lemma chainComparison_objects_bijective (hM : PositiveAcyclic M) :
    Function.Bijective (chainComparison M).objects := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he : (chainComparison M).map x.val = (chainComparison M).map y.val := congrArg Subtype.val h
    obtain ⟨⟨a,q⟩,hx,_⟩ := tensor_object_endpoint x.val x.property
    exact hx.trans ((chainComparison_endpoint_fiber y.val a q.val).mp
      (he.symm.trans ((chainComparison_endpoint_fiber x.val a q.val).mpr hx))).symm
  · intro t
    have hzero : CylinderTables.label t.val false = CylinderTables.label t.val true := by
      have hh := congrArg (fun z => CylinderTables.label z true) t.property
      change CylinderTables.label (truncate 0 false t.val) true = _ at hh
      erw [CylinderTables.label_truncate] at hh
      simpa only [ite_true] using hh
    have hc := CylinderTables.label_values hM t.val false
    have hex : ∃ a : Bool, t.val = (M.cylinderEndpoint a).table (CylinderTables.project t.val) := by
      rcases hc with hc | hc
      · exact ⟨false,CylinderTables.stationary_reconstruct hM t.val false hc (hzero.symm.trans hc)⟩
      · exact ⟨true,CylinderTables.stationary_reconstruct hM t.val true hc (hzero.symm.trans hc)⟩
    obtain ⟨a,ha⟩ := hex
    let q := M.cylinderProjection.nu.objects t
    refine ⟨((tensorEndpoint a).app M.nu).objects q,Subtype.ext ?_⟩
    exact (chainComparison_endpoint_apply a q.val).trans ha.symm
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma side_of_row_zero (t : Table M.cylinder) (a : Bool) (p : ℕ) (b : Bool)
    (h : t.row p b = 0) : side t a p b = 0 := by
  cases p with
  | zero => cases a; exact congrArg Prod.fst h; exact congrArg Prod.snd h
  | succ p => cases a; exact congrArg Prod.fst h; exact congrArg (fun x => x.2.1) h

lemma cross_of_row_zero (t : Table M.cylinder) (p : ℕ) (b : Bool)
    (h : t.row (p+1) b = 0) : cross t p b = 0 := congrArg (fun x => x.2.2) h

def crossingProfile (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1) :
    Table M where
  row := cross t
  positive := cross_positive t
  boundary := cross_boundary t
  augmentation := crossing_augmentation t hs ht
  bounded := by
    obtain ⟨n,hn⟩ := t.bounded
    exact ⟨n,fun p hp b => cross_of_row_zero t p b (hn (p+1) (by omega) b)⟩

def leftProfileRow (t : Table M.cylinder) (p : ℕ) (b : Bool) : M.Chain p :=
  side t false p b + if Even p then (if b then cross t p b else 0) else (if b then 0 else cross t p b)

def rightProfileRow (t : Table M.cylinder) (p : ℕ) (b : Bool) : M.Chain p :=
  side t true p b + if Even p then (if b then 0 else cross t p b) else (if b then cross t p b else 0)

lemma left_d (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t false (p+1) b) = side t false p true - side t false p false + (-1 : ℤ)^p • cross t p b :=
  eq_add_of_sub_eq (left_boundary t p b)

lemma right_d (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (side t true (p+1) b) = side t true p true - side t true p false - (-1 : ℤ)^p • cross t p b :=
  eq_sub_of_add_eq (right_boundary t p b)

lemma leftProfileRow_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (leftProfileRow t (p+1) b) = leftProfileRow t p true - leftProfileRow t p false := by
  unfold leftProfileRow
  simp only [Nat.even_add_one]
  by_cases hp : Even p <;> cases b <;>
    simp only [hp,not_true_eq_false,not_false_eq_true,ite_true,ite_false,Bool.false_eq_true,
      map_add,map_zero,left_d,cross_boundary,neg_one_pow_eq_ite,one_smul,neg_smul] <;> abel

lemma rightProfileRow_boundary (t : Table M.cylinder) (p : ℕ) (b : Bool) :
    M.d p (rightProfileRow t (p+1) b) = rightProfileRow t p true - rightProfileRow t p false := by
  unfold rightProfileRow
  simp only [Nat.even_add_one]
  by_cases hp : Even p <;> cases b <;>
    simp only [hp,not_true_eq_false,not_false_eq_true,ite_true,ite_false,Bool.false_eq_true,
      map_add,map_zero,right_d,cross_boundary,neg_one_pow_eq_ite,one_smul,neg_smul] <;> abel

def leftProfile (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1) : Table M where
  row := leftProfileRow t
  positive p b := by
    apply (M.positive p).add_mem (side_positive t false p b)
    split_ifs <;> first | exact cross_positive t p b | exact (M.positive p).zero_mem
  boundary := leftProfileRow_boundary t
  augmentation b := by
    have h := augmentation_sides t b
    have hc := crossing_augmentation t hs ht b
    cases b <;>
      simp only [leftProfileRow,Even.zero,ite_true,Bool.false_eq_true,ite_false,map_add,map_zero]
    · change M.augmentation (side t false 0 false) + label t false = 1 at h
      omega
    · change M.augmentation (side t false 0 true) + label t true = 1 at h
      omega
  bounded := by
    obtain ⟨n,hn⟩ := t.bounded
    refine ⟨n,fun p hp b => ?_⟩
    have ha := side_of_row_zero t false p b (hn p hp b)
    have hc := cross_of_row_zero t p b (hn (p+1) (by omega) b)
    simp only [leftProfileRow,ha,hc,ite_self,add_zero]

def rightProfile (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1) : Table M where
  row := rightProfileRow t
  positive p b := by
    apply (M.positive p).add_mem (side_positive t true p b)
    split_ifs <;> first | exact cross_positive t p b | exact (M.positive p).zero_mem
  boundary := rightProfileRow_boundary t
  augmentation b := by
    have hc := crossing_augmentation t hs ht b
    cases b <;>
      simp only [rightProfileRow,Even.zero,ite_true,Bool.false_eq_true,ite_false,map_add,map_zero]
    · change M.augmentation (side t true 0 false) = 0 at hs
      omega
    · simpa only [label,add_zero] using ht
  bounded := by
    obtain ⟨n,hn⟩ := t.bounded
    refine ⟨n,fun p hp b => ?_⟩
    have ha := side_of_row_zero t true p b (hn p hp b)
    have hc := cross_of_row_zero t p b (hn (p+1) (by omega) b)
    simp only [rightProfileRow,ha,hc,ite_self,add_zero]

lemma side_cylinder_map {N : DirectedComplex.{v}} (f : Hom M N) (t : Table M.cylinder)
    (a : Bool) (p : ℕ) (b : Bool) :
    side (f.cylinder.table t) a p b = f.map p (side t a p b) := by
  cases p <;> cases a <;> rfl

lemma cross_cylinder_map {N : DirectedComplex.{v}} (f : Hom M N) (t : Table M.cylinder)
    (p : ℕ) (b : Bool) : cross (f.cylinder.table t) p b = f.map p (cross t p b) := rfl

lemma crossingProfile_natural {N : DirectedComplex.{v}} (f : Hom M N) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hs' : label (f.cylinder.table t) false = 0) (ht' : label (f.cylinder.table t) true = 1) :
    crossingProfile (f.cylinder.table t) hs' ht' = f.table (crossingProfile t hs ht) := rfl

lemma leftProfile_natural {N : DirectedComplex.{v}} (f : Hom M N) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hs' : label (f.cylinder.table t) false = 0) (ht' : label (f.cylinder.table t) true = 1) :
    leftProfile (f.cylinder.table t) hs' ht' = f.table (leftProfile t hs ht) := by
  ext p b
  change leftProfileRow (f.cylinder.table t) p b = f.map p (leftProfileRow t p b)
  simp only [leftProfileRow,side_cylinder_map,cross_cylinder_map,map_add]
  split_ifs <;> simp only [map_zero]

lemma rightProfile_natural {N : DirectedComplex.{v}} (f : Hom M N) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hs' : label (f.cylinder.table t) false = 0) (ht' : label (f.cylinder.table t) true = 1) :
    rightProfile (f.cylinder.table t) hs' ht' = f.table (rightProfile t hs ht) := by
  ext p b
  change rightProfileRow (f.cylinder.table t) p b = f.map p (rightProfileRow t p b)
  simp only [rightProfileRow,side_cylinder_map,cross_cylinder_map,map_add]
  split_ifs <;> simp only [map_zero]

lemma project_profiles (t : Table M.cylinder) (hs : label t false = 0) (ht : label t true = 1)
    (p : ℕ) (b : Bool) :
    (project t).row p b = (leftProfile t hs ht).row p b + (rightProfile t hs ht).row p b -
      (crossingProfile t hs ht).row p b := by
  rw [project_row]
  change side t false p b + side t true p b = leftProfileRow t p b + rightProfileRow t p b - cross t p b
  unfold leftProfileRow rightProfileRow
  split_ifs <;> abel

lemma crossing_profiles_ext {t s : Table M.cylinder}
    (ht₀ : label t false = 0) (ht₁ : label t true = 1)
    (hs₀ : label s false = 0) (hs₁ : label s true = 1)
    (hcross : crossingProfile t ht₀ ht₁ = crossingProfile s hs₀ hs₁)
    (hleft : leftProfile t ht₀ ht₁ = leftProfile s hs₀ hs₁)
    (hright : rightProfile t ht₀ ht₁ = rightProfile s hs₀ hs₁) : t = s := by
  have hc (p : ℕ) (b : Bool) : cross t p b = cross s p b :=
    congrArg (fun x : Table M => x.row p b) hcross
  have hl (p : ℕ) (b : Bool) : side t false p b = side s false p b := by
    have h := congrArg (fun x : Table M => x.row p b) hleft
    change leftProfileRow t p b = leftProfileRow s p b at h
    unfold leftProfileRow at h
    rw [hc] at h
    exact add_right_cancel h
  have hr (p : ℕ) (b : Bool) : side t true p b = side s true p b := by
    have h := congrArg (fun x : Table M => x.row p b) hright
    change rightProfileRow t p b = rightProfileRow s p b at h
    unfold rightProfileRow at h
    rw [hc] at h
    exact add_right_cancel h
  ext p b
  cases p with
  | zero => exact Prod.ext (hl 0 b) (hr 0 b)
  | succ p => exact Prod.ext (hl (p+1) b) (Prod.ext (hr (p+1) b) (hc p b))
end Thomason.DirectedComplex.CylinderTables

end

end OAI
