import Mathlib
import OAI.Algebra.GroupRing.AttachmentFurther
import OAI.Algebra.GroupRing.CellularFurther2

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

namespace GroupRingTopology.Cellular
open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]

def skeletonInclusion (n : ℕ) : C(Skeleton C n,X) := ⟨Subtype.val,continuous_subtype_val⟩

/-- One step of the classical cellular approximation theorem, without any
local finiteness assumption on the target CW complex. -/
lemma deform_skeleton_succ (n : ℕ) (f : C(K,Skeleton C (n+1)))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Skeleton C n))
      (H : f.Homotopy ((skeletonBase n).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C n → H (t,x) = f x := by
  let e := skeletonHomeomorph (C := C) n
  let : T2Space (Attachment.Space (skeletonBoundary (C := C) n)) := e.symm.t2Space
  let f' : C(K,Attachment.Space (skeletonBoundary (C := C) n)) := (⟨e.symm,e.symm.continuous⟩ : C(_, _)).comp f
  obtain ⟨g,H,hH⟩ := Attachment.exists_deformation_into_base (skeletonBoundary (C := C) n) f' hdim
  have h0 : (⟨e,e.continuous⟩ : C(_, _)).comp f' = f := by apply ContinuousMap.ext; intro x; exact e.apply_symm_apply (f x)
  have h1 : (⟨e,e.continuous⟩ : C(_, _)).comp
      ((⟨Attachment.base _,Attachment.continuous_base _⟩ : C(_, _)).comp g) =
      (skeletonBase n).comp g := by apply ContinuousMap.ext; intro x; exact skeletonAssembly_base n (g x)
  let J := (ContinuousMap.Homotopy.refl (⟨e,e.continuous⟩ : C(_, _))).comp H
  refine ⟨g,J.cast h0 h1,?_⟩
  intro t x hx
  change e (H (t,x)) = f x
  have hr : f' x ∈ Set.range (Attachment.base (skeletonBoundary (C := C) n)) := by
    refine ⟨⟨(f x).1,hx⟩,?_⟩
    apply e.injective
    change skeletonAssembly n (Attachment.base _ _) = e (e.symm (f x))
    rw [skeletonAssembly_base,e.apply_symm_apply]
    rfl
  rw [hH t x hr]
  exact e.apply_symm_apply (f x)

/-- Bounded-skeleton cellular approximation with a stationary relative set:
all points initially in the target skeleton remain fixed. -/
lemma deform_bounded_skeleton (d m : ℕ) (f : C(K,Skeleton C m))
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d))
      (H : ((skeletonInclusion m).comp f).Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C d → H (t,x) = (f x).1 := by
  induction m with
  | zero =>
    let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono (Nat.zero_le d) (f x).2⟩,
      f.continuous.subtype_val.subtype_mk _⟩
    exact ⟨g,.refl _,fun _ _ _ => rfl⟩
  | succ m ih =>
    by_cases hmd : m+1 ≤ d
    · let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono hmd (f x).2⟩,
        f.continuous.subtype_val.subtype_mk _⟩
      exact ⟨g,.refl _,fun _ _ _ => rfl⟩
    · have hdm : d ≤ m := by omega
      obtain ⟨g,H,hH⟩ := deform_skeleton_succ m f (hdim.trans_le (by exact_mod_cast hdm))
      obtain ⟨g',J,hJ⟩ := ih g
      let H' := (ContinuousMap.Homotopy.refl (skeletonInclusion (C := C) (m+1))).comp H
      refine ⟨g',H'.trans J,?_⟩
      intro t x hx
      have hh (s : unitInterval) : H' (s,x) = (f x).1 := by
        exact congrArg Subtype.val (hH s x (skeleton_mono hdm hx))
      have hg : (g x).1 = (f x).1 := by
        have he := hh 1
        rw [ContinuousMap.Homotopy.apply_one] at he
        exact he
      have hj (s : unitInterval) : J (s,x) = (f x).1 := by
        rw [hJ s x (hg.symm ▸ hx),hg]
      erw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hh _
      · exact hj _

/-- Cellular approximation for arbitrary compact finite-Hausdorff-dimensional
sources. Compactness bounds the traversed dimensions, not the number of cells
of the whole CW complex. -/
theorem exists_cellular_approximation (d : ℕ) (f : C(K,X)) (hf : ∀ x,f x ∈ C)
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d)) (H : f.Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, f x ∈ Skeleton C d → H (t,x) = f x := by
  obtain ⟨m,hm⟩ := compactMap_bounded_skeleton f hf
  let f' : C(K,Skeleton C m) := ⟨fun x => ⟨f x,hm x⟩,f.continuous.subtype_mk _⟩
  exact deform_bounded_skeleton d m f' hdim
end GroupRingTopology.Cellular
namespace GroupRingTopology.SphereTopology
open Set Metric Topology
universe u
variable {Y : Type u} [TopologicalSpace Y]
lemma fill_zero [Nonempty Y] (a : C(Cellular.Sphere 0,Y)) :
    ∃ e : C(Cellular.Disk 0,Y), ∀ x, e (Cellular.boundary 0 x) = a x := by
  refine ⟨.const _ (Classical.choice ‹Nonempty Y›),?_⟩
  intro x
  have hx := x.2
  have hz : x.1 = 0 := Subsingleton.elim _ _
  simp only [hz,mem_sphere,dist_self] at hx
  exact False.elim (zero_ne_one hx)
lemma fill_one [PathConnectedSpace Y] (a : C(Cellular.Sphere 1,Y)) :
    ∃ e : C(Cellular.Disk 1,Y), ∀ x, e (Cellular.boundary 1 x) = a x := by
  let p := (PathConnectedSpace.joined (a Cayley.minus) (a Cayley.plus)).somePath
  let e : C(Cellular.Disk 1,Y) := p.toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
  refine ⟨e,?_⟩
  intro x
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,p.source]
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,p.target]
end GroupRingTopology.SphereTopology
namespace GroupRingTopology.Cellular
open Set Metric Topology
universe u v w
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A ghost map in one geometric degree, including unbased spheres. -/
def KillsSpheres (q : C(Y,Z)) (n : ℕ) : Prop :=
  ∀ a : C(Sphere n,Y), ∃ F : C(Disk n,Z), ∀ x, F (boundary n x) = q (a x)

lemma cylinder_filling_after {n : ℕ} (q : C(Y,Z)) (hq : KillsSpheres q (n+1))
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x)) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x t, e (boundary n x) t = q (a x t)) ∧
      ∀ x, pathEndpoint (e x) = (q (b x).1,q (b x).2) := by
  obtain ⟨F,hF⟩ := hq (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Z)) :=
    (F.comp ⟨fun p : Disk n × unitInterval => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = q (a x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change q (a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a x t)
    rw [diskTime_cons]
    congr 2
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = q (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 0))).1 = q (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = q (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 1))).2 = q (b x).2
      rw [diskTail_cons]

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

structure PartialHomotopy (f g : C(X,Y)) (n : ℕ) where
  val : X → C(unitInterval,Y)
  continuousOn : ContinuousOn val (Skeleton C n)
  zero : ∀ x ∈ Skeleton C n, val x 0 = f x
  one : ∀ x ∈ Skeleton C n, val x 1 = g x

namespace PartialHomotopy
variable {f g : C(X,Y)} {n : ℕ}

def onSphere (a : PartialHomotopy (C := C) f g n) (i : RelCWComplex.cell C n) :
    C(Sphere n,C(unitInterval,Y)) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

def endpoints (i : RelCWComplex.cell C n) : C(Disk n,Y × Y) :=
  ⟨fun x => (f (characteristic n i x),g (characteristic n i x)),
    (f.continuous.comp (characteristic n i).continuous).prodMk
      (g.continuous.comp (characteristic n i).continuous)⟩

lemma endpoints_compatible (a : PartialHomotopy (C := C) f g n)
    (i : RelCWComplex.cell C n) (x : Sphere n) :
    pathEndpoint (a.onSphere i x) = endpoints (f := f) (g := g) i (boundary n x) :=
  Prod.ext (a.zero _ (sphere_mem_skeleton n i x)) (a.one _ (sphere_mem_skeleton n i x))

lemma cell_extension_after (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x, e (boundary n x) = q.comp (a.val (characteristic n i (boundary n x)))) ∧
      (∀ x, e x 0 = q (f (characteristic n i x))) ∧
      (∀ x, e x 1 = q (g (characteristic n i x))) := by
  obtain ⟨e,he,hp⟩ := cylinder_filling_after q hq (a.onSphere i) (endpoints i)
    (a.endpoints_compatible i)
  exact ⟨e,fun x => ContinuousMap.ext (he x),fun x => congrArg Prod.fst (hp x),
    fun x => congrArg Prod.snd (hp x)⟩

/-- A single uniform ghost extends every partially constructed homotopy by a
whole CW dimension, even if there are infinitely many cells in that dimension. -/
def next (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) :
    PartialHomotopy (C := C) (q.comp f) (q.comp g) (n+1) := by
  let e := fun i => (a.cell_extension_after q hq i).choose
  have hb : ∀ i x, e i (boundary n x) =
      q.comp (a.val (characteristic n i (boundary n x))) :=
    fun i => (a.cell_extension_after q hq i).choose_spec.1
  have hz := fun i => (a.cell_extension_after q hq i).choose_spec.2.1
  have ho := fun i => (a.cell_extension_after q hq i).choose_spec.2.2
  let v : X → C(unitInterval,Z) := fun x => q.comp (a.val x)
  have hv : ContinuousOn v (Skeleton C n) :=
    (ContinuousMap.continuous_postcomp q).comp_continuousOn a.continuousOn
  refine ⟨attachValue v e,attachValue_continuous v hv e hb,?_,?_⟩
  all_goals
    intro x hx
    have heq : Skeleton C (n+1) = Skeleton C n ∪
        ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
      simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
        (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
    rw [heq] at hx
    rcases hx with hx | hx
    · rw [attachValue_old v e hx]
      first
      | exact congrArg q (a.zero x hx)
      | exact congrArg q (a.one x hx)
    · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
      rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
        attachValue_characteristic v e hb]
      first | exact hz i ⟨y,hy⟩ | exact ho i ⟨y,hy⟩

def start (f g : C(X,Y)) : PartialHomotopy (C := C) f g 0 where
  val := fun x => ContinuousMap.const _ (f x)
  continuousOn := by
    rw [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty]
    exact continuousOn_empty _
  zero := by intro x _; rfl
  one := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

/-- On a whole finite-dimensional complex the final partial homotopy is an
ordinary continuous homotopy, not merely cellwise data. -/
def toHomotopy [CWComplex (Set.univ : Set X)] (a : PartialHomotopy (C := (Set.univ : Set X)) f g n)
    (hdim : Skeleton (Set.univ : Set X) n = Set.univ) : f.Homotopy g where
  toFun p := a.val p.2 p.1
  continuous_toFun := by
    have hv : Continuous a.val := by
      have hh := a.continuousOn
      rw [hdim] at hh
      exact continuousOn_univ.mp hh
    exact continuous_eval.comp ((hv.comp continuous_snd).prodMk continuous_fst)
  map_zero_left x := a.zero x (hdim.symm ▸ Set.mem_univ x)
  map_one_left x := a.one x (hdim.symm ▸ Set.mem_univ x)

end PartialHomotopy
end GroupRingTopology.Cellular

namespace TorsionFreeZeroDivisors.FiniteDimensionalCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Cellular
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
/-- No higher cells really means that the indicated finite skeleton is the
whole space; no replacement by homology or a resolution is involved. -/
lemma skeleton_eq_univ (N : ℕ)
    (hdim : ∀ m : ℕ, N ≤ m → IsEmpty (RelCWComplex.cell (Set.univ : Set X) m)) :
    Skeleton (Set.univ : Set X) N=Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ ⋃m,⋃i : RelCWComplex.cell (Set.univ : Set X) m,CWComplex.openCell m i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    trivial
  obtain ⟨m,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  have hm : m<N := by
    by_contra h
    exact (hdim m (by omega)).false i
  exact CWComplex.mem_skeletonLT_iff.mpr ⟨m,by exact_mod_cast hm,i,hi⟩

/-- A two-dimensional CW contraction uses only fillings of circles and
2-spheres: extend the contraction over actual 0-, 1-, and 2-cells. This is the
needed special case of Whitehead, proved directly using cellular homotopy
extension from the supplied checked support. -/
theorem contractible_of_two_dimensional_fills [PathConnectedSpace X]
    (hdim : ∀ m : ℕ, 2 < m → IsEmpty (RelCWComplex.cell (Set.univ : Set X) m))
    (hcircle : ∀ a : C(SphereTopology.Sphere 2,X),SphereTopology.Extends a)
    (hsphere : ∀ a : C(SphereTopology.Sphere 3,X),SphereTopology.Extends a) :
    ContractibleSpace X := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let f : C(X,X) := ContinuousMap.id X
  let g : C(X,X) := ContinuousMap.const X x₀
  have h1 : KillsSpheres (ContinuousMap.id X) 1 := fun a=>SphereTopology.fill_one a
  have h2 : KillsSpheres (ContinuousMap.id X) 2 := by
    intro a
    obtain ⟨F,hF⟩ := hcircle a
    exact ⟨F,fun x=>ContinuousMap.congr_fun hF x⟩
  have h3 : KillsSpheres (ContinuousMap.id X) 3 := by
    intro a
    obtain ⟨F,hF⟩ := hsphere a
    exact ⟨F,fun x=>ContinuousMap.congr_fun hF x⟩
  let A := PartialHomotopy.start (C:=Set.univ) f g
  let B := A.next (ContinuousMap.id X) h1
  let C := B.next (ContinuousMap.id X) h2
  let D := C.next (ContinuousMap.id X) h3
  have hsk : Skeleton (Set.univ : Set X) 3=Set.univ :=
    skeleton_eq_univ 3 (fun m hm=>hdim m (by omega))
  have H : f.Homotopy g := D.toHomotopy hsk
  exact (contractible_iff_id_nullhomotopic X).mpr ⟨x₀,⟨H⟩⟩
end TorsionFreeZeroDivisors.FiniteDimensionalCW

namespace TorsionFreeZeroDivisors.PresentationTopology
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
variable {G S : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def pointCover : C(G,PUnit) := .const _ PUnit.unit
lemma pointCover_quotient : IsQuotientCoveringMap (pointCover (G := G)) G where
  __ := show IsQuotientMap (pointCover (G := G)) from
    (show IsOpenMap (pointCover (G := G)) from fun _ _ => isOpen_discrete _).isQuotientMap
      (by fun_prop) (fun _ => ⟨1,rfl⟩)
  __ := (inferInstance : ContinuousConstSMul G G)
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro _; exact ⟨x*y⁻¹,by simp [smul_eq_mul]⟩
    · intro _; rfl
  disjoint x := by
    refine ⟨{x},(isOpen_discrete _).mem_nhds (Set.mem_singleton x),?_⟩
    rintro g ⟨z,⟨y,hy,rfl⟩,h⟩
    simp only [Set.mem_singleton_iff] at hy h
    rw [hy] at h
    exact mul_right_cancel (show g*x=1*x by simpa only [smul_eq_mul,one_mul] using h)

variable (s : S → G)
def roseAttaching : S → C(Sphere 1,PUnit) := fun i=>(pointCover (G:=G)).comp (Cayley.attaching s i)
abbrev Rose := Space (roseAttaching s)
def graphProjection : C(Cayley.Graph s,Rose s) :=
  coverMap (Cayley.attaching s) pointCover pointCover_quotient (roseAttaching s) (fun _ _=>rfl)
lemma graphProjection_quotient : IsQuotientCoveringMap (graphProjection s) G :=
  coverMap_isQuotientCovering _ _ _ _ _
instance roseT2 : T2Space (Rose s) := t2Space _ realSeparated_of_tychonoff
instance roseCW : CWComplex (Set.univ : Set (Rose s)) :=
  layerCW _ Cayley.discrete_dimension
omit [DiscreteTopology G] in
lemma rose_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Rose s)) m) : m<2 :=
  layerCW_dimensions _ Cayley.discrete_dimension m i
omit [DiscreteTopology G] in
lemma rose_finite [Finite S] (m : ℕ) : Finite (RelCWComplex.cell (Set.univ : Set (Rose s)) m) := by
  apply layerCW_finite_cells
  intro n
  cases n with
  | zero => change Finite (Set.univ : Set PUnit); infer_instance
  | succ n => change Finite PEmpty; infer_instance
instance rosePathConnected : PathConnectedSpace (Rose s) := by
  let := SphereTopology.sphere_nonempty 0
  exact Attachment.pathConnectedSpace _

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r=1)
def diskAttaching : rels → C(Sphere 2,Rose s) := fun r=>
  (graphProjection s).comp (Cayley.relatorAttaching s rels hrel r)
abbrev Base := Space (diskAttaching s rels hrel)
def projection : C(Cayley.PresentationCover s rels hrel,Base s rels hrel) :=
  coverMap (Cayley.relatorAttaching s rels hrel) (graphProjection s)
    (graphProjection_quotient s) (diskAttaching s rels hrel) (fun _ _=>rfl)
lemma projection_quotient : IsQuotientCoveringMap (projection s rels hrel) G :=
  coverMap_isQuotientCovering _ _ _ _ _
instance baseT2 : T2Space (Base s rels hrel) :=
  t2Space _ (realSeparated _ realSeparated_of_tychonoff)
instance baseCW : CWComplex (Set.univ : Set (Base s rels hrel)) :=
  layerCW _ (rose_dimension s)
lemma base_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Base s rels hrel)) m) : m<3 :=
  layerCW_dimensions _ (rose_dimension s) m i
lemma base_no_higher (m : ℕ) (hm : 2 < m) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (Base s rels hrel)) m) :=
  ⟨fun i=>by have := base_dimension s rels hrel m i; omega⟩
lemma base_finite [Finite S] [Finite rels] : CWComplex.Finite (Set.univ : Set (Base s rels hrel)) where
  eventually_isEmpty_cell := Filter.eventually_atTop.mpr ⟨3,fun m hm=>base_no_higher s rels hrel m (by omega)⟩
  finite_cell m := layerCW_finite_cells _ (rose_finite s) (rose_dimension s) m
lemma base_two_cell (hr : rels.Nonempty) :
    Nonempty (RelCWComplex.cell (Set.univ : Set (Base s rels hrel)) 2) := by
  obtain ⟨r,hr⟩ := hr
  exact ⟨Sum.inr ⟨⟨⟨rfl⟩,⟨r,hr⟩⟩⟩⟩
instance basePathConnected : PathConnectedSpace (Base s rels hrel) := by
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
def coverPoint : Cayley.PresentationCover s rels hrel :=
  Cayley.presentationBase s rels hrel (Cayley.vertex s 1)
def basePoint : Base s rels hrel := projection s rels hrel (coverPoint s rels hrel)
lemma cover_no_higher (m : ℕ) (hm : 2 < m) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (Cayley.PresentationCover s rels hrel)) m) := by
  refine ⟨fun i=>?_⟩
  have := layerCW_dimensions (equivariantFamily (G:=G) (Cayley.relatorAttaching s rels hrel))
    (Cayley.graph_dimension s) m i
  omega

variable (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure rels)
def fundamentalEquiv : G ≃* FundamentalGroup (Base s rels hrel) (basePoint s rels hrel) := by
  let := Cayley.presentationCover_simplyConnected s rels hrel hs hker
  exact (MulEquiv.inv' G).trans
    ((projection_quotient s rels hrel).fundamentalGroupEquiv
      ⟨coverPoint s rels hrel,rfl⟩).symm

include hs hker in
lemma contractible_cover
    (hfill : ∀ a : C(Sphere 3,Cayley.PresentationCover s rels hrel),SphereTopology.Extends a) :
    ContractibleSpace (Cayley.PresentationCover s rels hrel) := by
  let := Cayley.presentationCover_pathConnected s rels hrel hs
  exact FiniteDimensionalCW.contractible_of_two_dimensional_fills
    (cover_no_higher s rels hrel) (Cayley.presentationCover_sphereFill s rels hrel hs hker) hfill

end TorsionFreeZeroDivisors.PresentationTopology

end

end OAI
