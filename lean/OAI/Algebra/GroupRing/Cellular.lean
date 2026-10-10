import Mathlib
import OAI.Algebra.GroupRing.Simplicial

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

omit [T2Space X] in
/-- Closure finiteness in terms of a single finite list of open cells. -/
lemma closedCell_subset_finite_openCells (n : ℕ) (i : RelCWComplex.cell C n) :
    ∃ I : Finset (Σ m, RelCWComplex.cell C m),
      CWComplex.closedCell n i ⊆ ⋃ p ∈ I, CWComplex.openCell p.1 p.2 := by
  classical
  obtain ⟨J,hJ⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
  refine ⟨insert ⟨n,i⟩ ((Finset.range n).sigma J),?_⟩
  intro x hx
  rw [← CWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
  rcases hx with hx | hx
  swap
  · exact Set.mem_iUnion.mpr ⟨⟨n,i⟩,Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,hx⟩⟩
  · have hxx := hJ hx
    simp only [Set.mem_iUnion] at hxx
    obtain ⟨m,hm,j,hj,hx⟩ := hxx
    exact Set.mem_iUnion.mpr ⟨⟨m,j⟩,Set.mem_iUnion.mpr
      ⟨Finset.mem_insert_of_mem (by simp only [Finset.mem_sigma,Finset.mem_range]; exact ⟨hm,hj⟩),hx⟩⟩

/-- Any selection of at most one point from each open cell has all its subsets
closed. This is the closure-finite weak-topology argument behind compactness. -/
lemma cellSelection_closed {I : Type u} (c : I → Σ n, RelCWComplex.cell C n)
    (hc : Function.Injective c) (x : I → X)
    (hx : ∀ i, x i ∈ CWComplex.openCell (c i).1 (c i).2) (S : Set X)
    (hS : S ⊆ Set.range x) : IsClosed S := by
  apply (CWComplex.closed C S ?_).mpr
  · intro n j
    obtain ⟨J,hJ⟩ := closedCell_subset_finite_openCells n j
    have hfinite : (S ∩ CWComplex.closedCell n j).Finite := by
      have hcpre : (c ⁻¹' (J : Set (Σ n, RelCWComplex.cell C n))).Finite :=
        J.finite_toSet.preimage hc.injOn
      apply (hcpre.image x).subset
      rintro y ⟨hyS,hycell⟩
      obtain ⟨i,rfl⟩ := hS hyS
      have hxx := hJ hycell
      simp only [Set.mem_iUnion] at hxx
      obtain ⟨p,hpJ,hxp⟩ := hxx
      have heq : c i = p := by
        by_contra hne
        exact (CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left (hx i) hxp
      exact ⟨i,by change c i ∈ J; rw [heq]; exact hpJ,rfl⟩
    exact hfinite.isClosed
  · rintro y hy
    obtain ⟨i,rfl⟩ := hS hy
    exact CWComplex.openCell_subset_complex (c i).1 (c i).2 (hx i)

/-- A compact part of a CW complex can meet only finitely many open cells. -/
theorem compact_finitely_many_cells {K : Set X} (hK : IsCompact K) :
    {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}.Finite := by
  classical
  let I := {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}
  let x : I → X := fun i => i.2.choose
  have hx (i : I) : x i ∈ CWComplex.openCell i.1.1 i.1.2 := i.2.choose_spec.2
  have hxK (i : I) : x i ∈ K := i.2.choose_spec.1
  have hinj : Function.Injective x := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact (CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left (hx i) (hij ▸ hx j)
  have hall : ∀ S ⊆ Set.range x, IsClosed S :=
    cellSelection_closed (C := C) Subtype.val Subtype.val_injective x hx
  have hcompact : IsCompact (Set.range x) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hxK)
  have hdiscrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdiscrete
  have : Finite I := (Set.finite_range_iff hinj).mp hrange
  exact Set.toFinite I

/-- Compact maps cannot run out through infinitely many dimensions. -/
theorem compact_bounded_skeleton {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ CWComplex.skeletonLT C n := by
  classical
  let S := {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hS : S.Finite := compact_finitely_many_cells hK
  let I := hS.toFinset
  refine ⟨I.sup (fun p => p.1+1),?_⟩
  intro x hx
  have hxC := hKC hx
  rw [← CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
  simp only [Set.mem_iUnion] at hxC
  obtain ⟨m,j,hj⟩ := hxC
  have hmem : (⟨m,j⟩ : Σ n, RelCWComplex.cell C n) ∈ I := by
    exact hS.mem_toFinset.mpr ⟨x,hx,hj⟩
  have hm : m+1 ≤ I.sup (fun p => p.1+1) := Finset.le_sup (f := fun p => p.1+1) hmem
  apply CWComplex.skeletonLT_mono (C := C)
    (m := (m : ℕ∞)+1) (n := ((I.sup (fun p => p.1+1) : ℕ) : ℕ∞)) (by exact_mod_cast hm)
  exact CWComplex.closedCell_subset_skeletonLT m j (CWComplex.openCell_subset_closedCell m j hj)

/-- The bounded-skeleton property in its map form, used for spheres and disks. -/
theorem compactMap_bounded_skeleton {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : C(A,X)) (hf : ∀ a, f a ∈ C) :
    ∃ n : ℕ, ∀ a, f a ∈ CWComplex.skeletonLT C n := by
  obtain ⟨n,hn⟩ := compact_bounded_skeleton (C := C) (isCompact_range f.continuous)
    (Set.range_subset_iff.mpr hf)
  exact ⟨n,fun a => hn (Set.mem_range_self a)⟩

end GroupRingTopology.Cellular

namespace GroupRingTopology.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

lemma compact_bounded_vertices {A : Set (Space K)} (hA : IsCompact A) :
    ∃ S : Finset V, ∀ x ∈ A, x.1.support ⊆ S := by
  let T := {p : Σ n, Topology.RelCWComplex.cell (Set.univ : Set (Space K)) n |
    (A ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hT : T.Finite := Cellular.compact_finitely_many_cells hA
  let S := hT.toFinset.biUnion (fun p => p.2.1.1)
  refine ⟨S,?_⟩
  intro x hx
  let s : Face K := ⟨x.1.support,x.2.2.2⟩
  let c := cellOfFace K s
  have hc : (⟨s.1.card-1,c⟩ : Σ n, Topology.RelCWComplex.cell (Set.univ : Set (Space K)) n) ∈ hT.toFinset := by
    rw [hT.mem_toFinset]
    refine ⟨x,hx,?_⟩
    change x ∈ characteristicPE K c '' ball 0 1
    rw [characteristicPE_open]
    rfl
  exact Finset.subset_biUnion_of_mem (fun p => p.2.1.1) hc

end GroupRingTopology.Simplicial

open Set Metric Topology
namespace GroupRingTopology.SphereTopology
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : C(Sphere n,Disk n) :=
  ⟨fun x => ⟨x.1,sphere_subset_closedBall x.2⟩,continuous_subtype_val.subtype_mk _⟩

lemma sphere_norm {n : ℕ} (x : Sphere n) : ‖x.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using x.2
lemma disk_norm {n : ℕ} (x : Disk n) : ‖x.1‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using x.2

def cone (n : ℕ) : C(unitInterval × Sphere n,Disk n) := by
  have hm (p : unitInterval × Sphere n) : (p.1:ℝ) • p.2.1 ∈ closedBall (0 : Fin n → ℝ) 1 := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.2.1,sphere_norm,mul_one]
    exact p.1.2.2
  exact ⟨fun p => ⟨(p.1:ℝ) • p.2.1,hm p⟩,
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk hm⟩

lemma cone_norm {n : ℕ} (p : unitInterval × Sphere n) : ‖(cone n p).1‖ = (p.1:ℝ) := by
  simp only [cone,ContinuousMap.coe_mk,norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.2.1,sphere_norm,mul_one]

lemma cone_surjective (n : ℕ) [Nonempty (Sphere n)] : Function.Surjective (cone n) := by
  intro x
  by_cases hx : x.1 = 0
  · obtain ⟨s⟩ := ‹Nonempty (Sphere n)›
    refine ⟨(0,s),Subtype.ext ?_⟩
    simp only [cone,ContinuousMap.coe_mk,Set.Icc.coe_zero,zero_smul,hx]
  · let s : Sphere n := ⟨‖x.1‖⁻¹ • x.1,by
      simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
    refine ⟨(⟨‖x.1‖,norm_nonneg _,disk_norm x⟩,s),Subtype.ext ?_⟩
    change ‖x.1‖ • (‖x.1‖⁻¹ • x.1) = x.1
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma cone_quotient (n : ℕ) [Nonempty (Sphere n)] : IsQuotientMap (cone n) :=
  IsQuotientMap.of_surjective_continuous (cone_surjective n) (cone n).continuous

variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

def Extends (f : C(Sphere n,Y)) : Prop := ∃ F : C(Disk n,Y), F.comp (boundary n) = f

lemma extends_of_nullhomotopic [Nonempty (Sphere n)] {y : Y} {f : C(Sphere n,Y)}
    (H : (ContinuousMap.const (Sphere n) y).Homotopy f) : Extends f := by
  have hf : Function.FactorsThrough H.toContinuousMap (cone n) := by
    intro p q hpq
    have ht : p.1 = q.1 := Subtype.ext ((cone_norm p).symm.trans ((congrArg (fun z : Disk n => ‖z.1‖) hpq).trans (cone_norm q)))
    by_cases hzero : (p.1:ℝ) = 0
    · have hp : p.1 = 0 := Subtype.ext hzero
      have hq : q.1 = 0 := ht.symm.trans hp
      change H (p.1,p.2) = H (q.1,q.2)
      rw [hp,hq,H.apply_zero,H.apply_zero]
      rfl
    · have hs : p.2 = q.2 := by
        apply Subtype.ext
        have heq := congrArg (fun z : Disk n => z.1) hpq
        change (p.1:ℝ) • p.2.1 = (q.1:ℝ) • q.2.1 at heq
        rw [← ht] at heq
        exact (smul_right_injective _ hzero) heq
      exact congrArg H.toContinuousMap (Prod.ext ht hs)
  let F : C(Disk n,Y) := (cone_quotient n).lift H.toContinuousMap hf
  refine ⟨F,?_⟩
  ext s
  have hh := ContinuousMap.congr_fun ((cone_quotient n).lift_comp H.toContinuousMap hf) (1,s)
  have hcone : cone n (1,s) = boundary n s := by apply Subtype.ext; simp [cone,boundary]
  simpa only [ContinuousMap.comp_apply,hcone,ContinuousMap.Homotopy.coe_toContinuousMap,
    ContinuousMap.Homotopy.apply_one] using hh

lemma nullhomotopic_of_extends {f : C(Sphere n,Y)} (hf : Extends f) :
    ∃ y : Y, Nonempty ((ContinuousMap.const (Sphere n) y).Homotopy f) := by
  obtain ⟨F,hF⟩ := hf
  let z : Disk n := ⟨0,by simp⟩
  refine ⟨F z,⟨{
    toFun := fun p => F (cone n p)
    continuous_toFun := F.continuous.comp (cone n).continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro s
    exact congrArg F (Subtype.ext (by simp [cone,z]))
  · intro s
    have hs : cone n (1,s) = boundary n s := by apply Subtype.ext; simp [cone,boundary]
    rw [hs]
    exact ContinuousMap.congr_fun hF s

lemma extends_of_homotopy [Nonempty (Sphere n)] {f g : C(Sphere n,Y)}
    (H : f.Homotopy g) (hg : Extends g) : Extends f := by
  obtain ⟨y,⟨J⟩⟩ := nullhomotopic_of_extends hg
  exact extends_of_nullhomotopic (J.trans H.symm)

lemma sphere_nonempty (n : ℕ) : Nonempty (Sphere (n+1)) :=
  (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)).coe_sort

end GroupRingTopology.SphereTopology

/-! Classical cellular lifting and its geometric foundations.
No classifying-space existence or Hurewicz theorem is assumed. -/
open Set Metric Topology

namespace GroupRingTopology.Cellular
universe u v w

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩

lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

/-- A characteristic map on its closed disk. -/
def characteristic (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n, X) :=
  ⟨fun x => RelCWComplex.map n i x.1, (RelCWComplex.continuousOn n i).domRestrict⟩

omit [T2Space X] in
lemma range_characteristic (n : ℕ) (i : RelCWComplex.cell C n) :
    Set.range (characteristic n i) = CWComplex.closedCell n i := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩; exact ⟨y.1,y.2,rfl⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨⟨y,hy⟩,rfl⟩

/-- The weak topology is genuinely final with respect to closed characteristic
maps; no finiteness or local-finiteness hypothesis is needed. -/
lemma continuousOn_iff_characteristic {Y : Type v} [TopologicalSpace Y] (f : X → Y) :
    ContinuousOn f C ↔ ∀ n (i : RelCWComplex.cell C n),
      Continuous (f ∘ characteristic n i) := by
  constructor
  · intro hf n i
    exact hf.comp_continuous (characteristic n i).continuous
      (fun x => CWComplex.closedCell_subset_complex n i ⟨x.1,x.2,rfl⟩)
  · intro hf
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_isClosed]
    intro S hS
    have hclosed : IsClosed (C ∩ f ⁻¹' S) := by
      apply (CWComplex.closed C _ inter_subset_left).2
      intro n i
      have hpre : IsClosed ((f ∘ characteristic n i) ⁻¹' S) :=
        hS.preimage (hf n i)
      have hcompact := hpre.isCompact.image (characteristic n i).continuous
      convert hcompact.isClosed using 1
      ext x
      constructor
      · rintro ⟨⟨hxC,hxS⟩, y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,hxS,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨CWComplex.closedCell_subset_complex n i ⟨y.1,y.2,rfl⟩,hy⟩,
          y.1,y.2,rfl⟩
    convert hclosed.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, and_iff_right x.2, Set.domRestrict_apply]

abbrev Skeleton (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  CWComplex.skeletonLT C n

lemma skeleton_mono {m n : ℕ} (h : m ≤ n) :
    Skeleton C m ⊆ Skeleton C n :=
  CWComplex.skeletonLT_mono (by exact_mod_cast h)

lemma sphere_mem_skeleton (n : ℕ) (i : RelCWComplex.cell C n) (x : Sphere n) :
    characteristic n i (boundary n x) ∈ Skeleton C n :=
  CWComplex.cellFrontier_subset_skeletonLT n i ⟨x.1,x.2,rfl⟩

lemma characteristic_mem_skeleton {m n : ℕ} (h : m < n)
    (i : RelCWComplex.cell C m) (x : Disk m) :
    characteristic m i x ∈ Skeleton C n := by
  apply skeleton_mono (Nat.succ_le_of_lt h)
  exact CWComplex.closedCell_subset_skeletonLT m i ⟨x.1,x.2,rfl⟩

lemma openCell_not_skeleton (n : ℕ) (i : RelCWComplex.cell C n) {x : X}
    (hx : x ∈ CWComplex.openCell n i) : x ∉ Skeleton C n :=
  (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_right hx

/-- A continuous partial lift on the (n-1)-skeleton, represented by a total
function only to avoid transported subtype terms. Values outside the skeleton
carry no condition and are never used. -/
structure PartialLift {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (f : C(X,B)) (n : ℕ) where
  val : X → E
  continuousOn : ContinuousOn val (Skeleton C n)
  fac : ∀ x ∈ Skeleton C n, p (val x) = f x

/-- The concrete disk-boundary right lifting property. -/
def DiskRLP {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) : Prop :=
  ∀ n (a : C(Sphere n,E)) (b : C(Disk n,B)),
    (∀ x, p (a x) = b (boundary n x)) →
    ∃ e : C(Disk n,E), (∀ x, e (boundary n x) = a x) ∧ ∀ x, p (e x) = b x

variable {E : Type v} [TopologicalSpace E] {n : ℕ}

/-- Glue the old skeleton map to a prescribed disk map on each new cell. -/
noncomputable def attachValue (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (x : X) : E := by
  classical
  exact if x ∈ Skeleton C n then a x
    else if h : ∃ i : RelCWComplex.cell C n, x ∈ CWComplex.openCell n i then
      let i := h.choose
      let y := h.choose_spec.choose
      e i ⟨y,ball_subset_closedBall h.choose_spec.choose_spec.1⟩
    else a x

lemma attachValue_old (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    {x : X} (hx : x ∈ Skeleton C n) : attachValue a e x = a x := by
  classical
  simp only [attachValue, ite_eq_left hx]

lemma attachValue_interior (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (i : RelCWComplex.cell C n) (y : Disk n) (hy : y.1 ∈ ball 0 1) :
    attachValue a e (characteristic n i y) = e i y := by
  classical
  have hx : characteristic n i y ∈ CWComplex.openCell n i := ⟨y.1,hy,rfl⟩
  have h : ∃ j : RelCWComplex.cell C n,
      characteristic n i y ∈ CWComplex.openCell n j := ⟨i,hx⟩
  rw [attachValue,ite_eq_right (openCell_not_skeleton n i hx),dite_eq_left h]
  have hi : h.choose = i := by
    by_contra hne
    have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := h.choose) (j := i)
      (fun hEq => hne (sigma_mk_injective hEq))
    exact Set.disjoint_left.mp hd h.choose_spec hx
  have hz := h.choose_spec.choose_spec.1
  have hmap : RelCWComplex.map n i h.choose_spec.choose = characteristic n i y := by
    calc
      RelCWComplex.map n i h.choose_spec.choose =
          RelCWComplex.map n h.choose h.choose_spec.choose :=
        congrArg (fun k => RelCWComplex.map n k h.choose_spec.choose) hi.symm
      _ = _ := h.choose_spec.choose_spec.2
  have hcoord : h.choose_spec.choose = y.1 :=
    (RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using hz)
      (by simpa only [RelCWComplex.source_eq] using hy) hmap
  exact (congrArg (fun k => e k ⟨h.choose_spec.choose,ball_subset_closedBall hz⟩) hi).trans
    (congrArg (e i) (Subtype.ext hcoord))

lemma attachValue_characteristic (a : X → E)
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x)))
    (i : RelCWComplex.cell C n) (y : Disk n) :
    attachValue a e (characteristic n i y) = e i y := by
  by_cases hy : y.1 ∈ ball 0 1
  · exact attachValue_interior a e i y hy
  · have hs : y.1 ∈ sphere 0 1 := le_antisymm y.2 (le_of_not_gt hy)
    have hx : characteristic n i y ∈ Skeleton C n := sphere_mem_skeleton n i ⟨y,hs⟩
    rw [attachValue_old a e hx]
    exact (he i ⟨y,hs⟩).symm

lemma attachValue_continuous (a : X → E) (ha : ContinuousOn a (Skeleton C n))
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x))) :
    ContinuousOn (attachValue a e) (Skeleton C (n+1)) := by
  apply (continuousOn_iff_characteristic (C := Skeleton C (n+1)) _).2
  intro m j
  change Continuous (fun x : Disk m => attachValue a e (characteristic m j.1 x))
  have hm : m < n+1 := by
    have h : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
      simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
    exact_mod_cast h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
  · have hEq : (fun x : Disk m => attachValue a e (characteristic m j.1 x)) =
        (fun x : Disk m => a (characteristic m j.1 x)) := by
      funext x
      exact attachValue_old a e (characteristic_mem_skeleton hm j.1 x)
    rw [hEq]
    exact ha.comp_continuous (characteristic m j.1).continuous
      (characteristic_mem_skeleton hm j.1)
  · subst m
    have hEq : (fun x : Disk n => attachValue a e (characteristic n j.1 x)) = e j.1 := by
      funext x
      exact attachValue_characteristic a e he j.1 x
    rw [hEq]
    exact (e j.1).continuous

end GroupRingTopology.Cellular

end

end OAI
