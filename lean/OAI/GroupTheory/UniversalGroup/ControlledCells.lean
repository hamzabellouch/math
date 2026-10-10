import OAI.GroupTheory.UniversalGroup.TreeGeometry

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Cellular

section
open Set Metric Topology
open scoped unitInterval
universe u v
variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

lemma square_filling_after {n : ℕ} (q : C(Y,Z)) (hq : KillsSpheres q (n+2))
    (a : C(Sphere n,C(I,C(I,Y))))
    (b c : C(Disk n,C(I,Y) × C(I,Y)))
    (hs : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (ht : ∀ x s, pathEndpoint (a x s) =
      ((c (boundary n x)).1 s,(c (boundary n x)).2 s))
    (h0 : ∀ x, pathEndpoint ((b x).1) = ((c x).1 0,(c x).2 0))
    (h1 : ∀ x, pathEndpoint ((b x).2) = ((c x).1 1,(c x).2 1)) :
    ∃ e : C(Disk n,C(I,C(I,Z))),
      (∀ x s t, e (boundary n x) s t = q (a x s t)) ∧
      (∀ x t, e x 0 t = q ((b x).1 t)) ∧
      (∀ x t, e x 1 t = q ((b x).2 t)) ∧
      (∀ x s, e x s 0 = q ((c x).1 s)) ∧
      (∀ x s, e x s 1 = q ((c x).2 s)) := by
  let A := cylinderBoundaryMap a b hs
  let B : C(Disk (n+1),Y × Y) :=
    ⟨fun x => ((c (diskTail x)).1 (diskTime x),(c (diskTail x)).2 (diskTime x)),by
      apply Continuous.prodMk
      · exact continuous_eval.comp
          ((continuous_fst.comp (c.continuous.comp continuous_diskTail)).prodMk continuous_diskTime)
      · exact continuous_eval.comp
          ((continuous_snd.comp (c.continuous.comp continuous_diskTail)).prodMk continuous_diskTime)⟩
  have hAB : ∀ x, pathEndpoint (A x) = B (boundary (n+1) x) := by
    intro x
    rcases sphere_split x with hx|hx|hx
    · have hx' : x ∈ cylinderFace n (some false) := hx
      rw [show A x = faceMap a b (some false) ⟨x,hx'⟩ from
        cylinderBoundaryMap_face a b hs (some false) ⟨x,hx'⟩]
      change pathEndpoint ((b (diskTail (boundary (n+1) x))).1) =
        ((c (diskTail (boundary (n+1) x))).1 (diskTime (boundary (n+1) x)),
        (c (diskTail (boundary (n+1) x))).2 (diskTime (boundary (n+1) x)))
      rw [faceTime_eq_zero x hx]; exact h0 _
    · have hx' : x ∈ cylinderFace n (some true) := hx
      rw [show A x = faceMap a b (some true) ⟨x,hx'⟩ from
        cylinderBoundaryMap_face a b hs (some true) ⟨x,hx'⟩]
      change pathEndpoint ((b (diskTail (boundary (n+1) x))).2) =
        ((c (diskTail (boundary (n+1) x))).1 (diskTime (boundary (n+1) x)),
        (c (diskTail (boundary (n+1) x))).2 (diskTime (boundary (n+1) x)))
      rw [faceTime_eq_one x hx]; exact h1 _
    · have hx' : x ∈ cylinderFace n none := hx
      rw [show A x = faceMap a b none ⟨x,hx'⟩ from
        cylinderBoundaryMap_face a b hs none ⟨x,hx'⟩]
      exact ht (faceSphere ⟨x,hx'⟩) (faceTime none ⟨x,hx'⟩)
  obtain ⟨d,hd,hp⟩ := cylinder_filling_after q hq A B hAB
  let e : C(Disk n,C(I,C(I,Z))) :=
    (d.comp ⟨fun p : Disk n × I => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_,?_,?_,?_⟩
  · intro x s t
    let z : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x s⟩
    have hz : z ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) s)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact x.2
    change d (diskCons (boundary n x) s) t = q (a x s t)
    rw [show diskCons (boundary n x) s = boundary (n+1) z from rfl,hd]
    rw [show A z = faceMap a b none ⟨z,hz⟩ from
      cylinderBoundaryMap_face a b hs none ⟨z,hz⟩]
    change q (a (faceSphere ⟨z,hz⟩) (diskTime (diskCons (boundary n x) s)) t) = _
    rw [diskTime_cons]; congr 2
  · intro x t
    let z : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
    have hz : z ∈ cylinderFace n (some false) := by
      change (diskCons x 0).1 0 = -1; norm_num [diskCons]
    change d (diskCons x 0) t = q ((b x).1 t)
    rw [show diskCons x 0 = boundary (n+1) z from rfl,hd]
    rw [show A z = faceMap a b (some false) ⟨z,hz⟩ from
      cylinderBoundaryMap_face a b hs (some false) ⟨z,hz⟩]
    change q ((b (diskTail (diskCons x 0))).1 t) = _
    rw [diskTail_cons]
  · intro x t
    let z : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
    have hz : z ∈ cylinderFace n (some true) := by
      change (diskCons x 1).1 0 = 1; norm_num [diskCons]
    change d (diskCons x 1) t = q ((b x).2 t)
    rw [show diskCons x 1 = boundary (n+1) z from rfl,hd]
    rw [show A z = faceMap a b (some true) ⟨z,hz⟩ from
      cylinderBoundaryMap_face a b hs (some true) ⟨z,hz⟩]
    change q ((b (diskTail (diskCons x 1))).2 t) = _
    rw [diskTail_cons]
  · intro x s
    have h := congrArg Prod.fst (hp (diskCons x s))
    change d (diskCons x s) 0 = _
    simpa only [pathEndpoint,ContinuousMap.coe_mk,B,ContinuousMap.coe_mk,
      diskTail_cons,diskTime_cons] using h
  · intro x s
    have h := congrArg Prod.snd (hp (diskCons x s))
    change d (diskCons x s) 1 = _
    simpa only [pathEndpoint,ContinuousMap.coe_mk,B,ContinuousMap.coe_mk,
      diskTail_cons,diskTime_cons] using h
end

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def postPath (q : C(Y,Z)) : C(C(I,Y),C(I,Z)) :=
  ⟨fun a => q.comp a,ContinuousMap.continuous_postcomp q⟩

structure SquareBoundary (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  b : C(X,C(I,Y) × C(I,Y))
  c : C(X,C(I,Y) × C(I,Y))
  zero : ∀ x, pathEndpoint ((b x).1) = ((c x).1 0,(c x).2 0)
  one : ∀ x, pathEndpoint ((b x).2) = ((c x).1 1,(c x).2 1)

namespace SquareBoundary

def post (D : SquareBoundary X Y) (q : C(Y,Z)) : SquareBoundary X Z where
  b := ⟨fun x => (postPath q (D.b x).1,postPath q (D.b x).2),
    ((postPath q).continuous.comp (continuous_fst.comp D.b.continuous)).prodMk
    ((postPath q).continuous.comp (continuous_snd.comp D.b.continuous))⟩
  c := ⟨fun x => (postPath q (D.c x).1,postPath q (D.c x).2),
    ((postPath q).continuous.comp (continuous_fst.comp D.c.continuous)).prodMk
    ((postPath q).continuous.comp (continuous_snd.comp D.c.continuous))⟩
  zero x := Prod.ext (congrArg q (congrArg Prod.fst (D.zero x)))
    (congrArg q (congrArg Prod.snd (D.zero x)))
  one x := Prod.ext (congrArg q (congrArg Prod.fst (D.one x)))
    (congrArg q (congrArg Prod.snd (D.one x)))
end SquareBoundary

variable [T2Space X] {C : Set X} [CWComplex C]

structure PartialSquare (D : SquareBoundary X Y) (n : ℕ) where
  val : X → C(I,C(I,Y))
  continuousOn : ContinuousOn val (Skeleton C n)
  left : ∀ x ∈ Skeleton C n, ∀ t, val x 0 t = (D.b x).1 t
  right : ∀ x ∈ Skeleton C n, ∀ t, val x 1 t = (D.b x).2 t
  bottom : ∀ x ∈ Skeleton C n, ∀ s, val x s 0 = (D.c x).1 s
  top : ∀ x ∈ Skeleton C n, ∀ s, val x s 1 = (D.c x).2 s

namespace PartialSquare
variable {D : SquareBoundary X Y} {n : ℕ}

def onSphere (P : PartialSquare (C := C) D n) (i : RelCWComplex.cell C n) :
    C(Sphere n,C(I,C(I,Y))) :=
  ⟨fun x => P.val (characteristic n i (boundary n x)),
    P.continuousOn.comp_continuous ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

lemma cell_extension_after (P : PartialSquare (C := C) D n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+2)) (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,C(I,C(I,Z))),
      (∀ x, e (boundary n x) = postPath (postPath q) (P.val (characteristic n i (boundary n x)))) ∧
      (∀ x t, e x 0 t = q ((D.b (characteristic n i x)).1 t)) ∧
      (∀ x t, e x 1 t = q ((D.b (characteristic n i x)).2 t)) ∧
      (∀ x s, e x s 0 = q ((D.c (characteristic n i x)).1 s)) ∧
      (∀ x s, e x s 1 = q ((D.c (characteristic n i x)).2 s)) := by
  obtain ⟨e,he,h0,h1,h2,h3⟩ := square_filling_after q hq (P.onSphere i)
    (D.b.comp (characteristic n i)) (D.c.comp (characteristic n i)) (by
      intro x; apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
      · exact P.left _ (sphere_mem_skeleton n i x) t
      · exact P.right _ (sphere_mem_skeleton n i x) t) (by
      intro x s; exact Prod.ext (P.bottom _ (sphere_mem_skeleton n i x) s)
        (P.top _ (sphere_mem_skeleton n i x) s))
    (fun x => D.zero (characteristic n i x)) (fun x => D.one (characteristic n i x))
  exact ⟨e,fun x => ContinuousMap.ext (fun s => ContinuousMap.ext (he x s)),h0,h1,h2,h3⟩

def next (P : PartialSquare (C := C) D n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+2)) : PartialSquare (C := C) (D.post q) (n+1) := by
  let e := fun i => (P.cell_extension_after q hq i).choose
  have hb := fun i => (P.cell_extension_after q hq i).choose_spec.1
  have h0 := fun i => (P.cell_extension_after q hq i).choose_spec.2.1
  have h1 := fun i => (P.cell_extension_after q hq i).choose_spec.2.2.1
  have h2 := fun i => (P.cell_extension_after q hq i).choose_spec.2.2.2.1
  have h3 := fun i => (P.cell_extension_after q hq i).choose_spec.2.2.2.2
  let v : X → C(I,C(I,Z)) := fun x => postPath (postPath q) (P.val x)
  have hv : ContinuousOn v (Skeleton C n) :=
    (postPath (postPath q)).continuous.comp_continuousOn P.continuousOn
  refine ⟨attachValue v e,attachValue_continuous v hv e hb,?_,?_,?_,?_⟩
  all_goals
    intro x hx t
    have heq : Skeleton C (n+1) = Skeleton C n ∪
        ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
      simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
        (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
    rw [heq] at hx
    rcases hx with hx|hx
    · rw [attachValue_old v e hx]
      first
      | exact congrArg q (P.left x hx t)
      | exact congrArg q (P.right x hx t)
      | exact congrArg q (P.bottom x hx t)
      | exact congrArg q (P.top x hx t)
    · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
      rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
        attachValue_characteristic v e hb]
      first
      | exact h0 i ⟨y,hy⟩ t
      | exact h1 i ⟨y,hy⟩ t
      | exact h2 i ⟨y,hy⟩ t
      | exact h3 i ⟨y,hy⟩ t

def start (D : SquareBoundary X Y) : PartialSquare (C := C) D 0 where
  val x := ContinuousMap.const _ (D.b x).1
  continuousOn := by
    rw [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty]
    exact continuousOn_empty _
  left := by intro x hx; simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx
  right := by intro x hx; simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx
  bottom := by intro x hx; simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx
  top := by intro x hx; simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

def toMap [CWComplex (Set.univ : Set X)]
    (P : PartialSquare (C := (Set.univ : Set X)) D n)
    (hd : Skeleton (Set.univ : Set X) n = Set.univ) : C(X,C(I,C(I,Y))) :=
  ⟨P.val,by
    apply continuousOn_univ.mp
    have h := P.continuousOn
    rw [hd] at h
    exact h⟩
end PartialSquare

end

open Set Metric Topology
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
variable (Y : ℕ → Type v) [∀ i,TopologicalSpace (Y i)] (q : ∀ i,C(Y i,Y (i+1)))

def boundaryTower (D : SquareBoundary X (Y 0)) : ∀ i,SquareBoundary X (Y i)
  | 0 => D
  | i+1 => (boundaryTower D i).post (q i)

variable (D : SquareBoundary X (Y 0)) (hq : ∀ i,KillsSpheres (q i) (i+2))

def squareTower : ∀ i,PartialSquare (C := (Set.univ : Set X)) (boundaryTower Y q D i) i
  | 0 => PartialSquare.start D
  | i+1 => (squareTower i).next (q i) (hq i)

include hq in

theorem exists_tower_square (d : ℕ) (hd : Skeleton (Set.univ : Set X) d = Set.univ) :
    ∃ S : C(X,C(I,C(I,Y d))),
      (∀ x t,S x 0 t = ((boundaryTower Y q D d).b x).1 t) ∧
      (∀ x t,S x 1 t = ((boundaryTower Y q D d).b x).2 t) ∧
      (∀ x s,S x s 0 = ((boundaryTower Y q D d).c x).1 s) ∧
      (∀ x s,S x s 1 = ((boundaryTower Y q D d).c x).2 s) := by
  let P := squareTower Y q D hq d
  refine ⟨P.toMap hd,?_,?_,?_,?_⟩
  · intro x t; exact P.left x (hd.symm ▸ Set.mem_univ x) t
  · intro x t; exact P.right x (hd.symm ▸ Set.mem_univ x) t
  · intro x s; exact P.bottom x (hd.symm ▸ Set.mem_univ x) s
  · intro x s; exact P.top x (hd.symm ▸ Set.mem_univ x) s
end UniversalFInfinity.Cellular

namespace UniversalFInfinity.SphereTopology
open Set Topology
open scoped unitInterval
universe u v w
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z] {n : ℕ} [Nonempty (Sphere n)]

lemma parametric_extension (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z))
    (a : C(B × Sphere n,Y)) :
    ∃ F : C(B × Disk n,Z), ∀ b x,F (b,boundary n x) = q (a (b,x)) := by
  let k : C(B × (I × Sphere n),B × Disk n) :=
    ⟨Prod.map id (cone n),continuous_fst.prodMk ((cone n).continuous.comp continuous_snd)⟩
  have hk : IsProperMap k := isProperMap_id.prodMap (cone n).continuous.isProperMap
  have hsurj : Function.Surjective k := Function.Surjective.prodMap Function.surjective_id (cone_surjective n)
  have hquot : IsQuotientMap k := hk.isClosedMap.isQuotientMap hk.continuous hsurj
  let v : C(B × (I × Sphere n),Z) :=
    ⟨fun p => H.symm (p.2.1,a (p.1,p.2.2)),H.symm.continuous.comp
      (continuous_snd.fst.prodMk (a.continuous.comp (continuous_fst.prodMk continuous_snd.snd)))⟩
  have hv : Function.FactorsThrough v k := by
    intro p r hpr
    have hb : p.1 = r.1 := congrArg (fun x : B × Disk n => x.1) hpr
    have hc : cone n p.2 = cone n r.2 := congrArg (fun x : B × Disk n => x.2) hpr
    have ht : p.2.1 = r.2.1 := Subtype.ext ((cone_norm p.2).symm.trans
      ((congrArg (fun x : Disk n => ‖x.1‖) hc).trans (cone_norm r.2)))
    by_cases hzero : (p.2.1:ℝ) = 0
    · have hp : p.2.1 = 0 := Subtype.ext hzero
      have hr : r.2.1 = 0 := ht.symm.trans hp
      change H.symm (p.2.1,a (p.1,p.2.2)) = H.symm (r.2.1,a (r.1,r.2.2))
      rw [hp,hr,H.symm.apply_zero,H.symm.apply_zero]
      rfl
    · have hs : p.2.2 = r.2.2 := by
        apply Subtype.ext
        have heq := congrArg (fun x : Disk n => x.1) hc
        change (p.2.1:ℝ) • p.2.2.1 = (r.2.1:ℝ) • r.2.2.1 at heq
        rw [←ht] at heq
        exact (smul_right_injective _ hzero) heq
      exact congrArg v (Prod.ext hb (Prod.ext ht hs))
  let F := hquot.lift v hv
  refine ⟨F,?_⟩
  intro b x
  have hh := ContinuousMap.congr_fun (hquot.lift_comp v hv) (b,(1,x))
  have hc : cone n (1,x) = boundary n x := by apply Subtype.ext; simp [cone,boundary]
  change F (b,cone n (1,x)) = H.symm (1,a (b,x)) at hh
  simpa only [hc,H.symm.apply_one,ContinuousMap.comp_apply] using hh
end UniversalFInfinity.SphereTopology

namespace UniversalFInfinity.Cellular

section
open Set Topology
open scoped unitInterval
universe u v
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y] {n : ℕ}
variable (a : C(B,C(Sphere n,C(I,Y)))) (b : C(B,C(Disk n,Y × Y)))
variable (h : ∀ v x,pathEndpoint (a v x) = b v (boundary n x))

def familyCylinderFace (i : Option Bool) : Set (B × Sphere (n+1)) :=
  Prod.snd ⁻¹' cylinderFace n i

def familyFaceMap (i : Option Bool) : C(familyCylinderFace (B := B) (n := n) i,Y) := by
  let π : C(familyCylinderFace (B := B) (n := n) i,B) := ⟨fun p => p.1.1,continuous_fst.comp continuous_subtype_val⟩
  let ρ : C(familyCylinderFace (B := B) (n := n) i,cylinderFace n i) :=
    ⟨fun p => ⟨p.1.2,p.2⟩,(continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
  cases i with
  | none => exact ⟨fun p => a (π p) (faceSphere (ρ p)) (faceTime none (ρ p)),
      continuous_eval.comp ((continuous_eval.comp ((a.continuous.comp π.continuous).prodMk
        (faceSphere.continuous.comp ρ.continuous))).prodMk ((faceTime none).continuous.comp ρ.continuous))⟩
  | some c =>
    cases c
    · exact ⟨fun p => (b (π p) (faceTail (some false) (ρ p))).1,
        continuous_fst.comp (continuous_eval.comp ((b.continuous.comp π.continuous).prodMk
          ((faceTail (some false)).continuous.comp ρ.continuous)))⟩
    · exact ⟨fun p => (b (π p) (faceTail (some true) (ρ p))).2,
        continuous_snd.comp (continuous_eval.comp ((b.continuous.comp π.continuous).prodMk
          ((faceTail (some true)).continuous.comp ρ.continuous)))⟩
lemma familyFaceMap_eq (i : Option Bool) (p : familyCylinderFace (B := B) (n := n) i) :
    familyFaceMap a b i p = faceMap (a p.1.1) (b p.1.1) i ⟨p.1.2,p.2⟩ := by
  cases i with
  | none => rfl
  | some c => cases c <;> rfl

include h in
lemma familyCylinder_continuous : Continuous (fun p : B × Sphere (n+1) => cylinderBoundaryMap (a p.1) (b p.1) (h p.1) p.2) := by
  let S := familyCylinderFace (B := B) (n := n)
  have hc : ∀ i j p (hi : p ∈ S i) (hj : p ∈ S j), familyFaceMap a b i ⟨p,hi⟩ = familyFaceMap a b j ⟨p,hj⟩ := by
    intro i j p hi hj
    rw [familyFaceMap_eq,familyFaceMap_eq]
    exact faceMap_compat (a p.1) (b p.1) (h p.1) i j p.2 hi hj
  have hcover : ⋃ i,S i = univ := by
    apply Set.eq_univ_of_forall
    intro p
    have hp : p.2 ∈ ⋃ i,cylinderFace n i := by rw [cylinderFace_cover]; exact mem_univ _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hclosed : ∀ i,IsClosed (S i) := fun i => (cylinderFace_closed n i).preimage continuous_snd
  have he : Set.liftCover S (fun i => familyFaceMap a b i) hc hcover =
      (fun p : B × Sphere (n+1) => cylinderBoundaryMap (a p.1) (b p.1) (h p.1) p.2) := by
    funext p
    have hp : p ∈ ⋃ i,S i := by rw [hcover]; exact mem_univ _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    rw [Set.liftCover_coe (S := S) (f := fun i => familyFaceMap a b i) (hf := hc) (hS := hcover) ⟨p,hi⟩,
      familyFaceMap_eq]
    exact (cylinderBoundaryMap_face (a p.1) (b p.1) (h p.1) i ⟨p.2,hi⟩).symm
  rw [←he]
  exact continuous_liftCover S _ hc hcover hclosed
end

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {B : Type u} [TopologicalSpace B] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
lemma family_cylinder_filling {n : ℕ} (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z))
    (a : C(B,C(Sphere n,C(I,Y)))) (b : C(B,C(Disk n,Y × Y)))
    (h : ∀ v x,pathEndpoint (a v x) = b v (boundary n x)) :
    ∃ e : C(B,C(Disk n,C(I,Z))),
      (∀ v x t,e v (boundary n x) t = q (a v x t)) ∧
      ∀ v x,pathEndpoint (e v x) = (q (b v x).1,q (b v x).2) := by
  let : Nonempty (Sphere (n+1)) := SphereTopology.sphere_nonempty n
  let a' : C(B × Sphere (n+1),Y) := ⟨_,familyCylinder_continuous a b h⟩
  obtain ⟨F,hF⟩ := SphereTopology.parametric_extension q z H a'
  change ∀ v x,F (v,boundary (n+1) x) = q (a' (v,x)) at hF
  let e : C(B,C(Disk n,C(I,Z))) :=
    (F.comp ⟨fun p : (B × Disk n) × I => (p.1.1,diskCons p.1.2 p.2),
      continuous_fst.fst.prodMk (continuous_diskCons.comp (continuous_fst.snd.prodMk continuous_snd))⟩).curry.curry
  refine ⟨e,?_,?_⟩
  · intro v x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact x.2
    change F (v,diskCons (boundary n x) t) = q (a v x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF]
    change q (cylinderBoundaryMap (a v) (b v) (h v) s) = _
    rw [cylinderBoundaryMap_face (a v) (b v) (h v) none ⟨s,hs⟩]
    change q (a v (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a v x t)
    rw [diskTime_cons]; congr 2
  · intro v x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1; norm_num [diskCons]
      change F (v,diskCons x 0) = q (b v x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF]
      change q (cylinderBoundaryMap (a v) (b v) (h v) s) = _
      rw [cylinderBoundaryMap_face (a v) (b v) (h v) (some false) ⟨s,hs⟩]
      change q (b v (diskTail (diskCons x 0))).1 = q (b v x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1; norm_num [diskCons]
      change F (v,diskCons x 1) = q (b v x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF]
      change q (cylinderBoundaryMap (a v) (b v) (h v) s) = _
      rw [cylinderBoundaryMap_face (a v) (b v) (h v) (some true) ⟨s,hs⟩]
      change q (b v (diskTail (diskCons x 1))).2 = q (b v x).2
      rw [diskTail_cons]
end

section
open Set Metric Topology
open scoped unitInterval
universe u v w
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
lemma family_square_filling {n : ℕ} (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z))
    (a : C(X,C(Sphere n,C(I,C(I,Y)))))
    (b c : C(X,C(Disk n,C(I,Y) × C(I,Y))))
    (hs : ∀ v x,pathEndpoint (a v x) = b v (boundary n x))
    (ht : ∀ v x s,pathEndpoint (a v x s) = ((c v (boundary n x)).1 s,(c v (boundary n x)).2 s))
    (h0 : ∀ v x,pathEndpoint ((b v x).1) = ((c v x).1 0,(c v x).2 0))
    (h1 : ∀ v x,pathEndpoint ((b v x).2) = ((c v x).1 1,(c v x).2 1)) :
    ∃ e : C(X,C(Disk n,C(I,C(I,Z)))),
      (∀ v x s t,e v (boundary n x) s t = q (a v x s t)) ∧
      (∀ v x t,e v x 0 t = q ((b v x).1 t)) ∧
      (∀ v x t,e v x 1 t = q ((b v x).2 t)) ∧
      (∀ v x s,e v x s 0 = q ((c v x).1 s)) ∧
      (∀ v x s,e v x s 1 = q ((c v x).2 s)) := by
  let A : C(X,C(Sphere (n+1),C(I,Y))) := ContinuousMap.curry ⟨_,familyCylinder_continuous a b hs⟩
  let B : C(X,C(Disk (n+1),Y × Y)) := ContinuousMap.curry
    ⟨fun p => ((c p.1 (diskTail p.2)).1 (diskTime p.2),(c p.1 (diskTail p.2)).2 (diskTime p.2)),by
      have hc : Continuous (fun p : X × Disk (n+1) => c p.1 (diskTail p.2)) :=
        continuous_eval.comp ((c.continuous.comp continuous_fst).prodMk (continuous_diskTail.comp continuous_snd))
      exact (continuous_eval.comp ((continuous_fst.comp hc).prodMk (continuous_diskTime.comp continuous_snd))).prodMk
        (continuous_eval.comp ((continuous_snd.comp hc).prodMk (continuous_diskTime.comp continuous_snd)))⟩
  have hAB : ∀ v x,pathEndpoint (A v x) = B v (boundary (n+1) x) := by
    intro v x
    rcases sphere_split x with hx|hx|hx
    · have hx' : x ∈ cylinderFace n (some false) := hx
      rw [show A v x = faceMap (a v) (b v) (some false) ⟨x,hx'⟩ from
        cylinderBoundaryMap_face (a v) (b v) (hs v) (some false) ⟨x,hx'⟩]
      change pathEndpoint ((b v (diskTail (boundary (n+1) x))).1) =
        ((c v (diskTail (boundary (n+1) x))).1 (diskTime (boundary (n+1) x)),
        (c v (diskTail (boundary (n+1) x))).2 (diskTime (boundary (n+1) x)))
      rw [faceTime_eq_zero x hx]; exact h0 v _
    · have hx' : x ∈ cylinderFace n (some true) := hx
      rw [show A v x = faceMap (a v) (b v) (some true) ⟨x,hx'⟩ from
        cylinderBoundaryMap_face (a v) (b v) (hs v) (some true) ⟨x,hx'⟩]
      change pathEndpoint ((b v (diskTail (boundary (n+1) x))).2) =
        ((c v (diskTail (boundary (n+1) x))).1 (diskTime (boundary (n+1) x)),
        (c v (diskTail (boundary (n+1) x))).2 (diskTime (boundary (n+1) x)))
      rw [faceTime_eq_one x hx]; exact h1 v _
    · have hx' : x ∈ cylinderFace n none := hx
      rw [show A v x = faceMap (a v) (b v) none ⟨x,hx'⟩ from
        cylinderBoundaryMap_face (a v) (b v) (hs v) none ⟨x,hx'⟩]
      exact ht v (faceSphere ⟨x,hx'⟩) (faceTime none ⟨x,hx'⟩)
  obtain ⟨d,hd,hp⟩ := family_cylinder_filling q z H A B hAB
  let e : C(X,C(Disk n,C(I,C(I,Z)))) :=
    (ContinuousMap.mk (fun p : (X × Disk n) × I => d p.1.1 (diskCons p.1.2 p.2))
      (continuous_eval.comp ((d.continuous.comp continuous_fst.fst).prodMk
        (continuous_diskCons.comp (continuous_fst.snd.prodMk continuous_snd))))).curry.curry
  refine ⟨e,?_,?_,?_,?_,?_⟩
  · intro v x s t
    let z' : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x s⟩
    have hz : z' ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) s)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact x.2
    change d v (diskCons (boundary n x) s) t = q (a v x s t)
    rw [show diskCons (boundary n x) s = boundary (n+1) z' from rfl,hd]
    rw [show A v z' = faceMap (a v) (b v) none ⟨z',hz⟩ from
      cylinderBoundaryMap_face (a v) (b v) (hs v) none ⟨z',hz⟩]
    change q (a v (faceSphere ⟨z',hz⟩) (diskTime (diskCons (boundary n x) s)) t) = _
    rw [diskTime_cons]; congr 2
  · intro v x t
    let z' : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
    have hz : z' ∈ cylinderFace n (some false) := by
      change (diskCons x 0).1 0 = -1; norm_num [diskCons]
    change d v (diskCons x 0) t = q ((b v x).1 t)
    rw [show diskCons x 0 = boundary (n+1) z' from rfl,hd]
    rw [show A v z' = faceMap (a v) (b v) (some false) ⟨z',hz⟩ from
      cylinderBoundaryMap_face (a v) (b v) (hs v) (some false) ⟨z',hz⟩]
    change q ((b v (diskTail (diskCons x 0))).1 t) = _
    rw [diskTail_cons]
  · intro v x t
    let z' : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
    have hz : z' ∈ cylinderFace n (some true) := by
      change (diskCons x 1).1 0 = 1; norm_num [diskCons]
    change d v (diskCons x 1) t = q ((b v x).2 t)
    rw [show diskCons x 1 = boundary (n+1) z' from rfl,hd]
    rw [show A v z' = faceMap (a v) (b v) (some true) ⟨z',hz⟩ from
      cylinderBoundaryMap_face (a v) (b v) (hs v) (some true) ⟨z',hz⟩]
    change q ((b v (diskTail (diskCons x 1))).2 t) = _
    rw [diskTail_cons]
  · intro v x s
    have h := congrArg Prod.fst (hp v (diskCons x s))
    change d v (diskCons x s) 0 = _
    simpa only [pathEndpoint,ContinuousMap.coe_mk,B,ContinuousMap.curry_apply,
      diskTail_cons,diskTime_cons] using h
  · intro v x s
    have h := congrArg Prod.snd (hp v (diskCons x s))
    change d v (diskCons x s) 1 = _
    simpa only [pathEndpoint,ContinuousMap.coe_mk,B,ContinuousMap.curry_apply,
      diskTail_cons,diskTime_cons] using h

lemma SquareBoundary.fill_after_nullhomotopy (D : SquareBoundary X Y)
    (q : C(Y,Z)) (z : Z) (H : q.Homotopy (.const _ z)) :
    ∃ Q : C(X,C(I,C(I,Z))),
      (∀ x t,Q x 0 t = q ((D.b x).1 t)) ∧
      (∀ x t,Q x 1 t = q ((D.b x).2 t)) ∧
      (∀ x s,Q x s 0 = q ((D.c x).1 s)) ∧
      (∀ x s,Q x s 1 = q ((D.c x).2 s)) := by
  let : IsEmpty (Sphere 0) := ⟨fun x => by
    have hx : x.1 = 0 := Subsingleton.elim _ _
    have h := x.2
    change ‖x.1‖ = 1 at h
    rw [hx,norm_zero] at h
    exact zero_ne_one h⟩
  let a : C(X,C(Sphere 0,C(I,C(I,Y)))) := .const _ ⟨isEmptyElim,continuous_of_discreteTopology⟩
  let b : C(X,C(Disk 0,C(I,Y) × C(I,Y))) := ContinuousMap.curry (D.b.comp .fst)
  let c : C(X,C(Disk 0,C(I,Y) × C(I,Y))) := ContinuousMap.curry (D.c.comp .fst)
  obtain ⟨e,_,h0,h1,h2,h3⟩ := family_square_filling q z H a b c (fun _ x => isEmptyElim x)
    (fun _ x => isEmptyElim x) (fun x _ => D.zero x) (fun x _ => D.one x)
  let x0 : Disk 0 := ⟨0,by simp⟩
  exact ⟨⟨fun x => e x x0,(continuous_eval_const x0).comp e.continuous⟩,
    fun x t => h0 x x0 t,fun x t => h1 x x0 t,fun x s => h2 x x0 s,fun x s => h3 x x0 s⟩
end

open Set Topology
open scoped unitInterval
universe u v w
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]
variable (a b : C(I × X,Y)) (A B : Y)
variable (h0 : ∀ x,a (0,x) = b (0,x)) (ha : ∀ x,a (1,x) = A) (hb : ∀ x,b (1,x) = B)

def contractionPath (a : C(I × X,Y)) (A : Y) (ha : ∀ x,a (1,x) = A) (x : X) : Path (a (0,x)) A :=
  { toFun t := a (t,x)
    continuous_toFun := a.continuous.comp (continuous_id.prodMk continuous_const)
    source' := rfl
    target' := ha x }

def connectorTop (x : X) : Path A B :=
  (contractionPath a A ha x).symm.trans ((contractionPath b B hb x).cast (h0 x) rfl)

def connectorSquare (x0 : X) : SquareBoundary X Y where
  b := (ContinuousMap.curry ((a.comp ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩).comp .fst)).prodMk
    (.const _ (connectorTop a b A B h0 ha hb x0).toContinuousMap)
  c := (ContinuousMap.curry (a.comp ⟨Prod.swap,continuous_swap⟩)).prodMk
    (ContinuousMap.curry (b.comp ⟨Prod.swap,continuous_swap⟩))
  zero x := Prod.ext rfl (h0 x)
  one x := Prod.ext ((connectorTop a b A B h0 ha hb x0).source.trans (ha x).symm)
    ((connectorTop a b A B h0 ha hb x0).target.trans (hb x).symm)

include h0 ha hb in

lemma connector_after_nullhomotopy (x0 : X) (q : C(Y,Z)) (z : Z)
    (H : q.Homotopy (.const _ z)) :
    ∃ (P : Path A B) (Q : C(X,C(I,C(I,Z)))),
      (∀ x t,Q x 0 t = q (a (0,x))) ∧
      (∀ x t,Q x 1 t = q (P t)) ∧
      (∀ x s,Q x s 0 = q (a (s,x))) ∧
      (∀ x s,Q x s 1 = q (b (s,x))) := by
  obtain ⟨Q,hQ0,hQ1,hQ2,hQ3⟩ := (connectorSquare a b A B h0 ha hb x0).fill_after_nullhomotopy q z H
  exact ⟨connectorTop a b A B h0 ha hb x0,Q,hQ0,hQ1,hQ2,hQ3⟩
end UniversalFInfinity.Cellular

end

end OAI
