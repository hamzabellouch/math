import Mathlib
import OAI.GroupTheory.FiniteType.SingularSigma

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
open Set Topology CWExtension CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

abbrev absolute (n : ℕ) := SingularChains.chains (Skel C n)
abbrev relative (n : ℕ) := CWSkeletalHomology.complex (C := C) n

def lowerHomeo (n : ℕ) : Skel C n ≃ₜ CWCollar.lower (C := C) n where
  toEquiv :=
    { toFun := fun x => ⟨skelIncl n x,x.2⟩
      invFun := fun x => ⟨x.1.1,x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (skelIncl n).continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def lowerIso (n : ℕ) : absolute (C := C) n ≅ SingularChains.chains (CWCollar.lower (C := C) n) := by
  letI := SingularChains.map_iso (lowerHomeo (C := C) n)
  exact asIso (SingularChains.map ((lowerHomeo (C := C) n) : C(_,_)))

def sequence (n : ℕ) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk ((lowerIso (C := C) n).hom ≫ (RelativeChains.sequence (CWCollar.lower n)).f)
    (RelativeChains.projection (CWCollar.lower n)) (by
      change ((lowerIso (C := C) n).hom ≫ (RelativeChains.sequence (CWCollar.lower n)).f) ≫ (RelativeChains.sequence (CWCollar.lower n)).g = 0
      erw [Category.assoc,(RelativeChains.sequence (CWCollar.lower (C := C) n)).zero,comp_zero])

lemma sequence_f (n : ℕ) : (sequence (C := C) n).f = SingularChains.map (skelIncl (C := C) n) := by
  dsimp only [sequence, lowerIso, RelativeChains.sequence, asIso_hom]
  rw [← SingularChains.map_comp]
  rfl

def sequenceIso (n : ℕ) : sequence (C := C) n ≅ RelativeChains.sequence (CWCollar.lower (C := C) n) :=
  ShortComplex.isoMk (lowerIso n) (Iso.refl _) (Iso.refl _)
    (by simp [sequence]; rfl) (by simp [sequence,RelativeChains.sequence])

lemma shortExact (n : ℕ) : (sequence (C := C) n).ShortExact :=
  ShortComplex.shortExact_of_iso (sequenceIso (C := C) n).symm (RelativeChains.shortExact _)

lemma above (n k : ℕ) (hk : n ≤ k) : Limits.IsZero ((absolute (C := C) n).homology k) := by
  induction n with
  | zero =>
    have he : Skel C 0 = ∅ := Topology.CWComplex.skeletonLT_zero_eq_empty
    let : IsEmpty (Skel C 0) := ⟨fun x => by simpa [he] using x.2⟩
    exact SingularChains.isEmpty_homology_isZero k
  | succ n ih =>
    have ha := ih (by omega)
    have hb := CWSkeletalHomology.homology_isZero (C := C) n k (by omega)
    exact ((shortExact (C := C) n).homology_exact₂ k).isZero_X₂
      (ha.eq_of_src _ _) (hb.eq_of_tgt _ _)

abbrev cell (n : ℕ) := (relative (C := C) n).homology n

def q (n k : ℕ) : (absolute (C := C) (n+1)).homology k ⟶ (relative (C := C) n).homology k :=
  homologyMap (sequence (C := C) n).g k

def delta (n : ℕ) : cell (C := C) (n+1) ⟶ (absolute (C := C) (n+1)).homology n :=
  (shortExact (C := C) (n+1)).δ (n+1) n rfl

lemma q_mono (n k : ℕ) (hk : n ≤ k) : Mono (q (C := C) n k) :=
  ((shortExact (C := C) n).homology_exact₂ k).mono_g ((above (C := C) n k hk).eq_of_src _ _)

def d (n : ℕ) : cell (C := C) (n+1) ⟶ cell (C := C) n := delta n ≫ q n n

lemma d_comp_d (n : ℕ) : d (C := C) (n+1) ≫ d n = 0 := by
  unfold d delta q
  erw [Category.assoc,← Category.assoc (homologyMap _ _) _ _]
  erw [(shortExact (C := C) (n+1)).comp_δ (n+1) n rfl,zero_comp,comp_zero]

def complex : ChainComplex (ModuleCat ℤ) ℕ := ChainComplex.of (cell (C := C)) d d_comp_d

lemma top_injective (n : ℕ) : Function.Injective (q (C := C) n n) := by
  let := q_mono (C := C) n n le_rfl
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

lemma q_d (n : ℕ) : q (C := C) (n+1) (n+1) ≫ d n = 0 := by
  unfold d delta q
  erw [← Category.assoc,(shortExact (C := C) (n+1)).comp_δ (n+1) n rfl,zero_comp]

lemma top_image (n : ℕ) (z : cell (C := C) (n+1)) :
    d n z = 0 ↔ ∃ x, q (C := C) (n+1) (n+1) x = z := by
  constructor
  · intro hz
    have hz' : delta (C := C) n z = 0 := by
      apply top_injective (C := C) n
      change q (C := C) n n (delta n z) = 0 at hz
      rw [map_zero]
      exact hz
    exact (ShortComplex.moduleCat_exact_iff _).mp
      ((shortExact (C := C) (n+1)).homology_exact₃ (n+1) n rfl) z hz'
  · rintro ⟨x,rfl⟩
    exact congrArg (fun f => f x) (q_d (C := C) n)

end CWCellular

namespace CWExtension
section
open Set Topology Metric
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

def skelLE {m n : ℕ} (h : m ≤ n) : C(Skel C m,Skel C n) :=
  ⟨fun x => ⟨x,RelCWComplex.skeletonLT_mono (by exact_mod_cast h) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def skelToComplex (n : ℕ) : C(Skel C n,C) :=
  ⟨fun x => ⟨x,(RelCWComplex.skeletonLT C n).subset_complex x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def wholeQuot : C((Σ n : ℕ,Skel C n),C) :=
  ⟨fun z => skelToComplex z.1 z.2,continuous_sigma (fun n => (skelToComplex n).continuous)⟩

theorem wholeQuot_surjective : Function.Surjective (wholeQuot (C := C)) := by
  intro x
  have hx : (x : X) ∈ ⋃ n : ℕ,(RelCWComplex.skeletonLT C n : Set X) := by
    rw [RelCWComplex.iUnion_skeletonLT_eq_complex]
    exact x.2
  obtain ⟨n,hn⟩ := mem_iUnion.mp hx
  exact ⟨⟨n,⟨x,hn⟩⟩,rfl⟩

theorem wholeQuot_isQuotientMap : IsQuotientMap (wholeQuot (C := C)) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨wholeQuot_surjective,fun S => ⟨fun h => h.preimage wholeQuot.continuous,?_⟩⟩
  intro hS
  apply isClosed_of_cells
  intro n i
  have hc : Continuous (fun v : Disk n => (⟨n+1,charSkel n i v⟩ : Σ m : ℕ,Skel C m)) :=
    continuous_sigmaMk.comp (charSkel n i).continuous
  exact hS.preimage hc

theorem family_compat (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) {m n : ℕ} (hmn : m ≤ n)
    (x : Skel C m) : F n (skelLE hmn x) = F m x := by
  induction n,hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact (hF n (skelLE hmn x)).trans ih

def familyData (F : ∀ n, C(Skel C n,Y)) : C((Σ n : ℕ,Skel C n),Y) :=
  ⟨fun z => F z.1 z.2,continuous_sigma (fun n => (F n).continuous)⟩

theorem familyData_factors (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) :
    Function.FactorsThrough (familyData F) wholeQuot := by
  rintro ⟨m,x⟩ ⟨n,y⟩ h
  have he : (x : X) = y := congrArg Subtype.val h
  change F m x = F n y
  rw [← family_compat F hF (le_max_left m n) x,
      ← family_compat F hF (le_max_right m n) y]
  exact congrArg (F (max m n)) (Subtype.ext he)

def unionMap (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) : C(C,Y) :=
  wholeQuot_isQuotientMap.lift (familyData F) (familyData_factors F hF)

@[simp] theorem unionMap_skel (F : ∀ n, C(Skel C n,Y))
    (hF : ∀ n x, F (n+1) (skelIncl n x) = F n x) (n : ℕ) (x : Skel C n) :
    unionMap F hF (skelToComplex n x) = F n x :=
  DFunLike.congr_fun (wholeQuot_isQuotientMap.lift_comp (familyData F) (familyData_factors F hF)) ⟨n,x⟩

end

open Set Topology Metric
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma finite_subset_skel {K : Set X} (hk : K.Finite) (hKC : K ⊆ C) : ∃ n : ℕ, K ⊆ Skel C n := by
  have h : ∀ K : Set X, K.Finite → K ⊆ C → ∃ n : ℕ, K ⊆ Skel C n := by
    intro K hK
    induction K,hK using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0,empty_subset _⟩
    | @insert x S hx hS ih =>
      intro hC
      obtain ⟨n,hn⟩ := ih (fun _ h => hC (mem_insert_of_mem _ h))
      have hxC := hC (mem_insert x S)
      have hxU : x ∈ ⋃ m : ℕ,Skel C m := by
        rw [RelCWComplex.iUnion_skeletonLT_eq_complex]
        exact hxC
      obtain ⟨m,hm⟩ := mem_iUnion.mp hxU
      refine ⟨max m n,?_⟩
      intro y hy
      rcases mem_insert_iff.mp hy with rfl | hy
      · exact RelCWComplex.skeletonLT_mono (by exact_mod_cast le_max_left m n) hm
      · exact RelCWComplex.skeletonLT_mono (by exact_mod_cast le_max_right m n) (hn hy)
  exact h K hk hKC

lemma compact_subset_skel {K : Set X} (hk : IsCompact K) (hKC : K ⊆ C) : ∃ n : ℕ, K ⊆ Skel C n := by
  classical
  by_contra hbound
  have hex (n : ℕ) : ∃ x, x ∈ K ∧ x ∉ Skel C n := by
    by_contra h
    apply hbound
    refine ⟨n,?_⟩
    intro x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  choose z hzK hzN using hex
  have hzC : range z ⊆ C := by rintro _ ⟨n,rfl⟩; exact hKC (hzK n)
  have hc (T : Set X) (hT : T ⊆ range z) : IsClosed T := by
    apply (CWComplex.closed C T (hT.trans hzC)).mpr
    intro m i
    apply Set.Finite.isClosed
    apply ((finite_Iio (m+1)).image z).subset
    rintro x ⟨hxT,hxcell⟩
    obtain ⟨n,rfl⟩ := hT hxT
    refine ⟨n,?_,rfl⟩
    change n < m+1
    by_contra hn
    exact hzN n (RelCWComplex.skeletonLT_mono (by exact_mod_cast (le_of_not_gt hn))
      (RelCWComplex.closedCell_subset_skeletonLT m i hxcell))
  have hd : IsDiscrete (range z) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T,hc T hT,inter_eq_left.mpr hT⟩
  have hkr : IsCompact (range z) := hk.of_isClosed_subset (hc _ (Subset.rfl)) (by
    rintro _ ⟨n,rfl⟩; exact hzK n)
  obtain ⟨n,hn⟩ := finite_subset_skel (hkr.finite hd) hzC
  exact hzN n (hn (mem_range_self n))

end CWExtension

end

end OAI
