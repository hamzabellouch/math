import OAI.GroupTheory.UniversalGroup.TopologicalTowers

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

namespace UniversalFInfinity.TopologicalTower

section
open Set Topology
universe u v w
variable {G : Type w} [Group G]
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, MulAction G (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

class EquivariantSystem : Prop where
  map_smul : ∀ i j h (g : G) x, f i j h (g • x) = g • f i j h x

variable [EquivariantSystem (G := G) X f]

instance limitMulAction : MulAction G (Space X f) where
  smul g := DirectLimit.lift f (fun n x => of X f n (g • x)) (fun i j h x => by
    rw [← EquivariantSystem.map_smul i j h g x,of_compat])
  one_smul z := by
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    change of X f n ((1:G) • x) = of X f n x
    rw [one_smul]
  mul_smul g h z := by
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    change of X f n ((g*h) • x) = of X f n (g • h • x)
    rw [mul_smul]

@[simp] lemma smul_of (g : G) (n : ℕ) (x : X n) :
    g • of X f n x = of X f n (g • x) := rfl

instance [∀ n, ContinuousConstSMul G (X n)] : ContinuousConstSMul G (Space X f) where
  continuous_const_smul g := (continuous_iff X f _).mpr (fun n =>
    (continuous_of X f n).comp (continuous_const_smul g))

end

section
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))
variable (k : ℕ) (U : ∀ n, k ≤ n → Set (X n))
variable (hU : ∀ i j (hi : k ≤ i) (hij : i ≤ j), f i j hij ⁻¹' U j (hi.trans hij) = U i hi)

def tailSet : Set (Space X f) := ⋃ n, ⋃ hn : k ≤ n, of X f n '' U n hn

include hf hU in
lemma preimage_tailSet (n : ℕ) (hn : k ≤ n) :
    of X f n ⁻¹' tailSet X f k U = U n hn := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,y,hy,hyx⟩ : ∃ j, ∃ (hj : k ≤ j), ∃ y ∈ U j hj,
        of X f j y = of X f n x := by simpa only [tailSet,Set.mem_preimage,Set.mem_iUnion,Set.mem_image] using hx
    let m := max j n
    have he : f j m (le_max_left _ _) y = f n m (le_max_right _ _) x :=
      of_injective X f hf m ((of_compat X f j m (le_max_left _ _) y).trans
        (hyx.trans (of_compat X f n m (le_max_right _ _) x).symm))
    have hym : f j m (le_max_left _ _) y ∈ U m (hj.trans (le_max_left _ _)) := by
      change y ∈ f j m (le_max_left _ _) ⁻¹' U m _
      rw [hU]
      exact hy
    rw [he] at hym
    change x ∈ f n m (le_max_right _ _) ⁻¹' U m _ at hym
    rw [hU] at hym
    exact hym
  · intro hx
    exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hn,⟨x,hx,rfl⟩⟩⟩

include hf hU in
lemma tailSet_isOpen (hopen : ∀ n hn, IsOpen (U n hn)) : IsOpen (tailSet X f k U) := by
  change @IsOpen _ (TopologicalSpace.coinduced (fun x : Σ n, X n => of X f x.1 x.2) inferInstance) _
  rw [isOpen_coinduced,isOpen_sigma_iff]
  intro n
  change IsOpen (of X f n ⁻¹' tailSet X f k U)
  rcases le_total k n with hn | hn
  · rw [preimage_tailSet X f hf k U hU n hn]
    exact hopen n hn
  · have heq : of X f n = of X f k ∘ f n k hn := (funext (of_compat X f n k hn)).symm
    rw [heq,Set.preimage_comp,preimage_tailSet X f hf k U hU k le_rfl]
    exact (hopen k le_rfl).preimage (f n k hn).continuous

end

section
open Set Topology
universe u w
variable {G : Type w} [Group G]
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, MulAction G (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable [EquivariantSystem (G := G) X f]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

structure Slice (n : ℕ) where
  carrier : Set (X n)
  isOpen : IsOpen carrier
  disjoint : ∀ g : G, ((g • ·) '' carrier ∩ carrier).Nonempty → g = 1

def ExtendsSlices : Prop := ∀ n (U : Slice (G := G) X n),
  ∃ V : Slice (G := G) X (n+1), f n (n+1) (Nat.le_succ n) ⁻¹' V.carrier = U.carrier

variable (hext : ExtendsSlices (G := G) X f)

def extendSlice (n : ℕ) (U : Slice (G := G) X n) : Slice (G := G) X (n+1) := (hext n U).choose

omit [DirectedSystem X (f · · ·)] [EquivariantSystem (G := G) X f] in
lemma extendSlice_spec (n : ℕ) (U : Slice (G := G) X n) :
    f n (n+1) (Nat.le_succ n) ⁻¹' (extendSlice X f hext n U).carrier = U.carrier :=
  (hext n U).choose_spec

def sliceFamily (k : ℕ) (U : Slice (G := G) X k) (n : ℕ) (hn : k ≤ n) : Slice (G := G) X n :=
  Nat.leRecOn hn (fun {m} => extendSlice X f hext m) U

omit [DirectedSystem X (f · · ·)] [EquivariantSystem (G := G) X f] in
lemma sliceFamily_self (k : ℕ) (U : Slice (G := G) X k) : sliceFamily X f hext k U k le_rfl = U := by
  simp only [sliceFamily,Nat.leRecOn_self]

omit [EquivariantSystem (G := G) X f] in
lemma sliceFamily_compat (k : ℕ) (U : Slice (G := G) X k) (i j : ℕ)
    (hi : k ≤ i) (hij : i ≤ j) :
    f i j hij ⁻¹' (sliceFamily X f hext k U j (hi.trans hij)).carrier =
      (sliceFamily X f hext k U i hi).carrier := by
  induction j,hij using Nat.le_induction with
  | base => ext x; simp only [Set.mem_preimage,DirectedSystem.map_self']
  | succ j hij ih =>
    unfold sliceFamily
    rw [Nat.leRecOn_succ (hi.trans hij)]
    have hcomp : f i (j+1) (hij.trans (Nat.le_succ j)) =
        f j (j+1) (Nat.le_succ j) ∘ f i j hij := by
      ext x
      exact (DirectedSystem.map_map' f hij (Nat.le_succ j) x).symm
    change (f i (j+1) _) ⁻¹' (extendSlice X f hext j _).carrier = _
    rw [hcomp,Set.preimage_comp,extendSlice_spec]
    exact ih

include hf in
lemma tailSet_disjoint (k : ℕ) (U : ∀ n, k ≤ n → Set (X n))
    (hU : ∀ i j (hi : k ≤ i) (hij : i ≤ j), f i j hij ⁻¹' U j (hi.trans hij) = U i hi)
    (hd : ∀ n hn (g : G), ((g • ·) '' U n hn ∩ U n hn).Nonempty → g = 1) :
    ∀ g : G, ((g • ·) '' tailSet X f k U ∩ tailSet X f k U).Nonempty → g = 1 := by
  intro g hg
  obtain ⟨_,⟨z,hz,rfl⟩,hgz⟩ := hg
  obtain ⟨j,x,rfl⟩ := DirectLimit.exists_eq_mk f z
  let m := max k j
  have he : of X f j x = of X f m (f j m (le_max_right _ _) x) :=
    (of_compat X f j m (le_max_right _ _) x).symm
  change of X f j x ∈ tailSet X f k U at hz
  rw [he] at hz
  change of X f m _ ∈ tailSet X f k U at hz
  have hmz := (Set.ext_iff.mp (preimage_tailSet X f hf k U hU m (le_max_left _ _)) _).mp hz
  change g • of X f j x ∈ tailSet X f k U at hgz
  rw [he,smul_of] at hgz
  have hmgz := (Set.ext_iff.mp (preimage_tailSet X f hf k U hU m (le_max_left _ _)) _).mp hgz
  exact hd m (le_max_left _ _) g ⟨_,⟨_,hmz,rfl⟩,hmgz⟩

include hf hext in
lemma exists_disjoint_nhds
    (hstage : ∀ n (x : X n), ∃ U ∈ 𝓝 x,
      ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ z : Space X f, ∃ U ∈ 𝓝 z, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  intro z
  obtain ⟨k,x,rfl⟩ := DirectLimit.exists_eq_mk f z
  obtain ⟨U,hUx,hU⟩ := hstage k x
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUx
  let S : Slice (G := G) X k := ⟨V,hV,fun g hg => hU g
    (hg.mono (Set.inter_subset_inter (Set.image_mono hVU) hVU))⟩
  let W := fun n hn => (sliceFamily X f hext k S n hn).carrier
  have hW := sliceFamily_compat X f hext k S
  refine ⟨tailSet X f k W,?_,tailSet_disjoint X f hf k W hW
    (fun n hn => (sliceFamily X f hext k S n hn).disjoint)⟩
  apply (tailSet_isOpen X f hf k W hW (fun n hn => (sliceFamily X f hext k S n hn).isOpen)).mem_nhds
  change of X f k x ∈ tailSet X f k W
  have hw : x ∈ W k le_rfl := by simpa only [W,sliceFamily_self] using hxV
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨le_rfl,⟨x,hw,rfl⟩⟩⟩

end

section
open Set Topology
universe u v w
variable {G : Type w} [Group G]
variable (E : ℕ → Type u) [∀ n, TopologicalSpace (E n)] [∀ n, MulAction G (E n)]
variable (e : ∀ i j, i ≤ j → C(E i,E j)) [DirectedSystem E (e · · ·)]
variable [EquivariantSystem (G := G) E e] [∀ n, ContinuousConstSMul G (E n)]
variable (X : ℕ → Type v) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (p : ∀ n, C(E n,X n))
variable (hp : ∀ i j h x, p j (e i j h x) = f i j h (p i x))

def limitMap : C(Space E e,Space X f) :=
  ⟨DirectLimit.lift e (fun n x => of X f n (p n x)) (fun i j h x => by
    rw [hp,of_compat]), (continuous_iff E e _).mpr (fun n =>
      (continuous_of X f n).comp (p n).continuous)⟩

@[simp] lemma limitMap_of (n : ℕ) (x : E n) :
    limitMap E e X f p hp (of E e n x) = of X f n (p n x) := rfl

omit [EquivariantSystem (G := G) E e] [∀ n, ContinuousConstSMul G (E n)] in
lemma limitMap_isQuotient (hq : ∀ n, IsQuotientMap (p n)) :
    IsQuotientMap (limitMap E e X f p hp) := by
  refine ⟨?_,?_⟩
  · rw [isCoinducing_iff]
    intro U
    constructor
    · intro hU
      change @IsOpen _ (TopologicalSpace.coinduced (fun z : Σ n, X n => of X f z.1 z.2)
        inferInstance) U
      rw [isOpen_coinduced,isOpen_sigma_iff]
      intro n
      apply (hq n).isOpen_preimage.mp
      exact hU.preimage (continuous_of E e n)
    · exact fun hU => hU.preimage (limitMap E e X f p hp).continuous
  · intro z
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    obtain ⟨y,rfl⟩ := (hq n).surjective x
    exact ⟨of E e n y,rfl⟩

omit [∀ n, ContinuousConstSMul G (E n)] in
lemma limitMap_fibers (hf : ∀ i j h, IsClosedEmbedding (f i j h))
    (hq : ∀ n, IsQuotientCoveringMap (p n) G) (x y : Space E e) :
    limitMap E e X f p hp x = limitMap E e X f p hp y ↔ x ∈ MulAction.orbit G y := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk e x
  obtain ⟨j,y,rfl⟩ := DirectLimit.exists_eq_mk e y
  let n := max i j
  change limitMap E e X f p hp (of E e i x) = limitMap E e X f p hp (of E e j y) ↔
    of E e i x ∈ MulAction.orbit G (of E e j y)
  rw [← of_compat E e i n (le_max_left _ _) x,← of_compat E e j n (le_max_right _ _) y]
  simp only [limitMap_of]
  constructor
  · intro hh
    have hh' := of_injective X f hf n hh
    obtain ⟨g,hg⟩ := (hq n).apply_eq_iff_mem_orbit.mp hh'
    exact ⟨g,congrArg (of E e n) hg⟩
  · rintro ⟨g,hg⟩
    have hh := congrArg (limitMap E e X f p hp) hg
    simpa only [smul_of,limitMap_of,(hq n).map_smul] using hh.symm

lemma limitMap_isQuotientCovering
    (he : ∀ i j h, IsClosedEmbedding (e i j h))
    (hf : ∀ i j h, IsClosedEmbedding (f i j h))
    (hq : ∀ n, IsQuotientCoveringMap (p n) G)
    (hext : ExtendsSlices (G := G) E e) :
    IsQuotientCoveringMap (limitMap E e X f p hp) G where
  __ := limitMap_isQuotient E e X f p hp (fun n => (hq n).toIsQuotientMap)
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := limitMap_fibers E e X f p hp hf hq _ _
  disjoint := exists_disjoint_nhds E e he hext (fun n => (hq n).disjoint)

end

open Set Metric Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, T1Space (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in
lemma compactMap_factors {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : C(A,Space X f)) :
    ∃ (n : ℕ) (a : C(A,X n)), ∀ x, of X f n (a x) = g x := by
  obtain ⟨n,hn⟩ := compact_bounded X f hf (isCompact_range g.continuous)
  have hex (x : A) : ∃ y, of X f n y = g x := hn (Set.mem_range_self x)
  choose a ha using hex
  have hcont : Continuous a := by
    apply (of_closedEmbedding X f hf n).isEmbedding.continuous_iff.mpr
    have heq : of X f n ∘ a = g := funext ha
    rw [heq]
    exact g.continuous
  exact ⟨n,⟨a,hcont⟩,ha⟩

def EventuallyFills : Prop := ∀ n k (a : C(Cellular.Sphere n,X k)),
  ∃ (j : ℕ) (hkj : k ≤ j) (b : C(Cellular.Disk n,X j)),
    ∀ x, b (Cellular.boundary n x) = f k j hkj (a x)

include hf in
lemma sphereFillable (hfill : EventuallyFills X f) : Cellular.SphereFillable (Space X f) := by
  intro n a
  obtain ⟨k,a',ha'⟩ := compactMap_factors X f hf a
  obtain ⟨j,hkj,b,hb⟩ := hfill n k a'
  refine ⟨⟨of X f j ∘ b,(continuous_of X f j).comp b.continuous⟩,?_⟩
  intro x
  change of X f j (b (Cellular.boundary n x)) = a x
  rw [hb,of_compat,ha']

include hf in

lemma contractible [T2Space (Space X f)] [Nonempty (Space X f)]
    [CWComplex (Set.univ : Set (Space X f))] (hfill : EventuallyFills X f) :
    ContractibleSpace (Space X f) :=
  Cellular.contractible_of_sphereFillable (sphereFillable X f hf hfill)

end UniversalFInfinity.TopologicalTower

end

end OAI
