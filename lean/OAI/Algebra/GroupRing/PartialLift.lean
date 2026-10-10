import Mathlib
import OAI.Algebra.GroupRing.Cellular

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
namespace GroupRingTopology.Cellular
universe u v w
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

namespace PartialLift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}

/-- The boundary lift for attaching an n-cell. -/
def onSphere (a : PartialLift (C := C) p f n) (i : RelCWComplex.cell C n) :
    C(Sphere n,E) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous
      ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

lemma exists_cell_extension (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,E),
      (∀ x, e (boundary n x) = a.val (characteristic n i (boundary n x))) ∧
      ∀ x, p (e x) = f (characteristic n i x) := by
  apply hp n (a.onSphere i) (f.comp (characteristic n i))
  intro x
  exact a.fac _ (sphere_mem_skeleton n i x)

/-- Extend a partial lift across all cells of the next dimension. -/
noncomputable def next (a : PartialLift (C := C) p f n) (hp : DiskRLP p) :
    PartialLift (C := C) p f (n+1) := by
  choose e hb hf using fun i => a.exists_cell_extension hp i
  refine ⟨attachValue a.val e,attachValue_continuous a.val a.continuousOn e hb,?_⟩
  intro x hx
  have hdecomp : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  rw [hdecomp] at hx
  rcases hx with hx | hx
  · rw [attachValue_old a.val e hx]
    exact a.fac x hx
  · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
      attachValue_characteristic a.val e hb]
    exact hf i ⟨y,hy⟩

lemma next_eq (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    {x : X} (hx : x ∈ Skeleton C n) : (a.next hp).val x = a.val x := by
  dsimp only [next]
  exact attachValue_old a.val _ hx

noncomputable def zero [Nonempty E] : PartialLift (C := C) p f 0 where
  val := fun _ => Classical.choice ‹Nonempty E›
  continuousOn := continuous_const.continuousOn
  fac := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

end PartialLift

section Lift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))

noncomputable def stages : ∀ n, PartialLift (C := C) p f n
  | 0 => PartialLift.zero
  | n+1 => (stages n).next hp

lemma stages_agree {m n : ℕ} (h : m ≤ n) {x : X} (hx : x ∈ Skeleton C m) :
    (stages (C := C) hp f n).val x = (stages (C := C) hp f m).val x := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ((stages (C := C) hp f n).next_eq hp (skeleton_mono hn hx)).trans ih

lemma exists_skeleton {x : X} (hx : x ∈ C) : ∃ n : ℕ, x ∈ Skeleton C n := by
  rw [← CWComplex.iUnion_skeletonLT_eq_complex (C := C)] at hx
  exact Set.mem_iUnion.mp hx

noncomputable def liftValue (x : X) : E := by
  classical
  exact if hx : x ∈ C then (stages (C := C) hp f (exists_skeleton (C := C) hx).choose).val x
    else Classical.choice ‹Nonempty E›

lemma liftValue_eq {n : ℕ} {x : X} (hx : x ∈ Skeleton C n) :
    liftValue (C := C) hp f x = (stages (C := C) hp f n).val x := by
  classical
  have hxC : x ∈ C := (CWComplex.skeletonLT C n).subset_complex hx
  rw [liftValue,dite_eq_left hxC]
  let m := (exists_skeleton (C := C) hxC).choose
  have hm : x ∈ Skeleton C m := (exists_skeleton (C := C) hxC).choose_spec
  exact (stages_agree hp f (Nat.le_max_left m n) hm).symm.trans
    (stages_agree hp f (Nat.le_max_right m n) hx)

lemma continuousOn_liftValue : ContinuousOn (liftValue (C := C) hp f) C := by
  apply (continuousOn_iff_characteristic _).2
  intro n i
  have hEq : liftValue (C := C) hp f ∘ characteristic n i =
      (stages (C := C) hp f (n+1)).val ∘ characteristic n i := by
    funext x
    exact liftValue_eq hp f (characteristic_mem_skeleton (Nat.lt_succ_self n) i x)
  rw [hEq]
  exact (stages (C := C) hp f (n+1)).continuousOn.comp_continuous (characteristic n i).continuous
    (characteristic_mem_skeleton (Nat.lt_succ_self n) i)

lemma liftValue_fac {x : X} (hx : x ∈ C) : p (liftValue (C := C) hp f x) = f x := by
  obtain ⟨n,hn⟩ := exists_skeleton (C := C) hx
  rw [liftValue_eq hp f hn]
  exact (stages (C := C) hp f n).fac x hn

include hp in
theorem exists_lift [CWComplex (Set.univ : Set X)] :
    ∃ g : C(X,E), ∀ x, p (g x) = f x := by
  refine ⟨⟨liftValue (C := Set.univ) hp f,
    continuousOn_univ.mp (continuousOn_liftValue (C := Set.univ) hp f)⟩,?_⟩
  intro x
  exact liftValue_fac hp f (Set.mem_univ x)

end Lift

noncomputable section
/-- Extension property with respect to the actual sup-norm disks. -/
def SphereFillable (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ n (a : C(Sphere n,Y)), ∃ e : C(Disk n,Y), ∀ x, e (boundary n x) = a x

lemma disk_coord {n : ℕ} (x : Disk n) (i : Fin n) : |x.1 i| ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mp
    (mem_closedBall_zero_iff.mp x.2) i

lemma disk_mem {n : ℕ} {x : Fin n → ℝ} (h : ∀ i, |x i| ≤ 1) :
    x ∈ closedBall 0 1 := by
  exact mem_closedBall_zero_iff.mpr
    ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr h)

def diskCons {n : ℕ} (x : Disk n) (t : unitInterval) : Disk (n+1) :=
  ⟨Fin.cons (2*t.1-1) x.1, disk_mem (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero,abs_le]
      constructor <;> linarith [t.2.1,t.2.2]
    · exact disk_coord x j)⟩

lemma continuous_diskCons {n : ℕ} :
    Continuous (fun q : Disk n × unitInterval => diskCons q.1 q.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun q : Disk n × unitInterval => 2*q.2.1-1)
    fun_prop
  · change Continuous (fun q : Disk n × unitInterval => q.1.1 j)
    exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)

def diskTail {n : ℕ} (x : Disk (n+1)) : Disk n :=
  ⟨Fin.tail x.1,disk_mem (fun i => disk_coord x i.succ)⟩

lemma continuous_diskTail {n : ℕ} : Continuous (@diskTail n) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)

def diskTime {n : ℕ} (x : Disk (n+1)) : unitInterval :=
  ⟨(x.1 0+1)/2,by have h := (abs_le.mp (disk_coord x 0)); constructor <;> linarith⟩

lemma continuous_diskTime {n : ℕ} : Continuous (@diskTime n) := by
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2 |>.subtype_mk _

@[simp] lemma diskTail_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTail (diskCons x t) = x := by
  apply Subtype.ext
  simp only [diskTail,diskCons,Fin.tail_cons]

@[simp] lemma diskTime_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTime (diskCons x t) = t := by
  apply Subtype.ext
  simp only [diskTime,diskCons,Fin.cons_zero]
  ring

lemma sphere_iff_coord {n : ℕ} (x : Disk n) :
    x.1 ∈ sphere 0 1 ↔ ∃ i, |x.1 i| = 1 := by
  rw [sphere_pi (0 : Fin n → ℝ) (Or.inl (by norm_num))]
  simp only [Set.mem_inter_iff,Set.mem_iUnion,Set.mem_preimage,Function.eval,
    Pi.zero_apply,mem_sphere_zero_iff_norm,Real.norm_eq_abs,and_iff_left x.2]

lemma cons_mem_sphere_of_boundary {n : ℕ} (x : Sphere n) (t : unitInterval) :
    (diskCons (boundary n x) t).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary n x)).mp x.2
  exact (sphere_iff_coord _).mpr ⟨i.succ,hi⟩

lemma cons_zero_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 0).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩

lemma cons_one_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 1).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩

lemma sphere_split {n : ℕ} (x : Sphere (n+1)) :
    x.1 0 = -1 ∨ x.1 0 = 1 ∨ (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary (n+1) x)).mp x.2
  refine Fin.cases ?_ (fun i hi => ?_) i hi
  · intro h
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact Or.inr (Or.inr ((sphere_iff_coord _).mpr ⟨i,hi⟩))

/-- Finite closed pasting, in a form usable for the three cylinder faces. -/
lemma continuous_liftCover {A : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace A] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set A) (f : ∀ i, C(S i,Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hcover : ⋃ i, S i = Set.univ) (hclosed : ∀ i, IsClosed (S i)) :
    Continuous (Set.liftCover S (fun i => f i) hcompat hcover) := by
  rw [continuous_iff_isClosed]
  intro D hD
  rw [Set.preimage_liftCover]
  exact isClosed_iUnion_of_finite fun i => (hclosed i).isClosedMap_subtype_val _ (hD.preimage (f i).continuous)

def cylinderFace (n : ℕ) : Option Bool → Set (Sphere (n+1))
  | none => {x | (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1}
  | some false => {x | x.1 0 = -1}
  | some true => {x | x.1 0 = 1}

lemma cylinderFace_closed (n : ℕ) (i : Option Bool) : IsClosed (cylinderFace n i) := by
  cases i with
  | none =>
    exact isClosed_sphere.preimage
      (continuous_subtype_val.comp (continuous_diskTail.comp (continuous_boundary (n+1))))
  | some b =>
    cases b <;>
      exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const

lemma cylinderFace_cover (n : ℕ) : ⋃ i, cylinderFace n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases sphere_split x with h | h | h
  · exact Set.mem_iUnion.mpr ⟨some false,h⟩
  · exact Set.mem_iUnion.mpr ⟨some true,h⟩
  · exact Set.mem_iUnion.mpr ⟨none,h⟩

variable {Y : Type u} [TopologicalSpace Y]

def pathEndpoint : C(C(unitInterval,Y), Y × Y) :=
  ⟨fun q => (q 0,q 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

section CylinderMap
variable {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))

def faceTail (i : Option Bool) : C(cylinderFace n i,Disk n) :=
  ⟨fun x => diskTail (boundary (n+1) x.1),
    continuous_diskTail.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩

def faceSphere : C(cylinderFace n none,Sphere n) :=
  ⟨fun x => ⟨(faceTail none x).1,x.2⟩, (continuous_subtype_val.comp (faceTail none).continuous).subtype_mk _⟩

def faceTime (i : Option Bool) : C(cylinderFace n i,unitInterval) :=
  ⟨fun x => diskTime (boundary (n+1) x.1),
    continuous_diskTime.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩

def faceMap : ∀ i : Option Bool, C(cylinderFace n i,Y)
  | none => ⟨fun x => a (faceSphere x) (faceTime none x),
      continuous_eval.comp ((a.continuous.comp faceSphere.continuous).prodMk (faceTime none).continuous)⟩
  | some false => ⟨fun x => (b (faceTail (some false) x)).1,
      continuous_fst.comp (b.continuous.comp (faceTail (some false)).continuous)⟩
  | some true => ⟨fun x => (b (faceTail (some true) x)).2,
      continuous_snd.comp (b.continuous.comp (faceTail (some true)).continuous)⟩

lemma faceTime_eq_zero (x : Sphere (n+1)) (h : x.1 0 = -1) :
    diskTime (boundary (n+1) x) = 0 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 0
  rw [h]
  norm_num

lemma faceTime_eq_one (x : Sphere (n+1)) (h : x.1 0 = 1) :
    diskTime (boundary (n+1) x) = 1 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 1
  rw [h]
  norm_num

variable (h : ∀ x, pathEndpoint (a x) = b (boundary n x))

include h in
lemma faceMap_compat (i j : Option Bool) (x : Sphere (n+1))
    (hi : x ∈ cylinderFace n i) (hj : x ∈ cylinderFace n j) :
    faceMap a b i ⟨x,hi⟩ = faceMap a b j ⟨x,hj⟩ := by
  have left (hs : x ∈ cylinderFace n none) (h0 : x.1 0 = -1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).1 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_zero x h0]
    exact congrArg Prod.fst (h (faceSphere ⟨x,hs⟩))
  have right (hs : x ∈ cylinderFace n none) (h1 : x.1 0 = 1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).2 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_one x h1]
    exact congrArg Prod.snd (h (faceSphere ⟨x,hs⟩))
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some c => cases c; exact left hi hj; exact right hi hj
  | some c =>
    cases c
    · cases j with
      | none => exact (left hj hi).symm
      | some d =>
        cases d
        · rfl
        · have := hi.symm.trans hj; norm_num at this
    · cases j with
      | none => exact (right hj hi).symm
      | some d =>
        cases d
        · have := hi.symm.trans hj; norm_num at this
        · rfl

def cylinderBoundaryMap : C(Sphere (n+1),Y) :=
  ⟨Set.liftCover (cylinderFace n) (fun i => faceMap a b i)
    (faceMap_compat a b h) (cylinderFace_cover n),
    continuous_liftCover _ _ _ _ (cylinderFace_closed n)⟩

lemma cylinderBoundaryMap_face (i : Option Bool) (x : cylinderFace n i) :
    cylinderBoundaryMap a b h x.1 = faceMap a b i x :=
  by
    apply Set.liftCover_coe (S := cylinderFace n) (f := fun i => faceMap a b i)
      (hf := faceMap_compat a b h) (hS := cylinderFace_cover n)

end CylinderMap

/-- A disk filling extends the three compatible boundary faces of a cylinder. -/
theorem pathEndpoint_RLP (hY : SphereFillable Y) : DiskRLP (@pathEndpoint Y _) := by
  intro n a b h
  obtain ⟨F,hF⟩ := hY (n+1) (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]

theorem contractible_of_sphereFillable {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [Nonempty Z] [CWComplex (Set.univ : Set Z)] (hZ : SphereFillable Z) :
    ContractibleSpace Z := by
  classical
  let z₀ : Z := Classical.choice ‹Nonempty Z›
  let : Nonempty C(unitInterval,Z) := ⟨ContinuousMap.const _ z₀⟩
  let f : C(Z,Z × Z) := ⟨fun z => (z,z₀),continuous_id.prodMk continuous_const⟩
  obtain ⟨g,hg⟩ := exists_lift (pathEndpoint_RLP hZ) f
  apply (contractible_iff_id_nullhomotopic Z).mpr
  refine ⟨z₀,⟨?_⟩⟩
  refine ContinuousMap.Homotopy.mk ⟨fun q => g q.2 q.1,
    continuous_eval.comp ((g.continuous.comp continuous_snd).prodMk continuous_fst)⟩ ?_ ?_
  · intro z
    exact congrArg Prod.fst (hg z)
  · intro z
    exact congrArg Prod.snd (hg z)

end
end GroupRingTopology.Cellular

end OAI
