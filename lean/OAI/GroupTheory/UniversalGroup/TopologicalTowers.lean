import OAI.GroupTheory.UniversalGroup.CellularFillings

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
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

abbrev Space := DirectLimit X f

def of (n : ℕ) (x : X n) : Space X f := ⟦⟨n,x⟩⟧

instance : TopologicalSpace (Space X f) :=
  TopologicalSpace.coinduced (fun x : Σ n, X n => of X f x.1 x.2) inferInstance

lemma of_compat (i j : ℕ) (h : i ≤ j) (x : X i) :
    of X f j (f i j h x) = of X f i x := DirectLimit.mk_apply i j x h

lemma continuous_iff {Y : Type v} [TopologicalSpace Y] (g : Space X f → Y) :
    Continuous g ↔ ∀ n, Continuous (g ∘ of X f n) := by
  rw [continuous_coinduced_dom,continuous_sigma_iff]
  rfl

lemma continuous_of (n : ℕ) : Continuous (of X f n) := by
  have h : Continuous (fun x : Σ n, X n => of X f x.1 x.2) := continuous_coinduced_rng
  exact h.comp continuous_sigmaMk

lemma isClosed_iff (A : Set (Space X f)) :
    IsClosed A ↔ ∀ n, IsClosed (of X f n ⁻¹' A) := by
  rw [isClosed_coinduced]
  exact isClosed_sigma_iff

variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in
lemma of_injective (n : ℕ) : Function.Injective (of X f n) :=
  DirectLimit.mk_injective f (fun i j h => (hf i j h).injective) n

include hf in
lemma preimage_of_image_le (i j : ℕ) (h : i ≤ j) (A : Set (X i)) :
    of X f j ⁻¹' (of X f i '' A) = f i j h '' A := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    refine ⟨x,hx,?_⟩
    apply of_injective X f hf j
    exact (of_compat X f i j h x).trans hxy
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(of_compat X f i j h x).symm⟩

include hf in
lemma preimage_of_image_ge (i j : ℕ) (h : j ≤ i) (A : Set (X i)) :
    of X f j ⁻¹' (of X f i '' A) = f j i h ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    have he : x = f j i h y := of_injective X f hf i
      (hxy.trans (of_compat X f j i h y).symm)
    change f j i h y ∈ A
    rw [← he]
    exact hx
  · intro hA
    exact ⟨f j i h y,hA,of_compat X f j i h y⟩

include hf in
lemma of_closedEmbedding (n : ℕ) : IsClosedEmbedding (of X f n) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_of X f n) (of_injective X f hf n)
  intro A hA
  rw [isClosed_iff]
  intro m
  rcases le_total n m with h | h
  · rw [preimage_of_image_le X f hf n m h]
    exact (hf n m h).isClosedMap _ hA
  · rw [preimage_of_image_ge X f hf n m h]
    exact hA.preimage (hf m n h).continuous

def lift {Y : Type v} [TopologicalSpace Y] (g : ∀ n, C(X n,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) : C(Space X f,Y) :=
  ⟨DirectLimit.lift f (fun n => g n) hg,
    (continuous_iff X f _).mpr (fun n => (g n).continuous)⟩

@[simp] lemma lift_of {Y : Type v} [TopologicalSpace Y] (g : ∀ n, C(X n,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) (n : ℕ) (x : X n) :
    lift X f g hg (of X f n x) = g n x := rfl

def tailLift {Y : Type v} [TopologicalSpace Y] (n : ℕ)
    (g : ∀ m, n ≤ m → C(X m,Y))
    (hg : ∀ i j (hi : n ≤ i) (hij : i ≤ j) x,
      g i hi x = g j (hi.trans hij) (f i j hij x)) : C(Space X f,Y) := by
  let G (m : ℕ) : C(X m,Y) :=
    ⟨fun x => g (max n m) (le_max_left _ _) (f m (max n m) (le_max_right _ _) x),
      (g _ _).continuous.comp (hf _ _ _).continuous⟩
  apply lift X f G
  intro i j hij x
  let k := max n j
  have hik : max n i ≤ k := max_le_max_left n hij
  change g (max n i) _ (f i (max n i) _ x) = g k _ (f j k _ (f i j hij x))
  rw [hg _ _ _ hik,DirectedSystem.map_map',DirectedSystem.map_map']

lemma tailLift_of {Y : Type v} [TopologicalSpace Y] (n : ℕ)
    (g : ∀ m, n ≤ m → C(X m,Y))
    (hg : ∀ i j (hi : n ≤ i) (hij : i ≤ j) x,
      g i hi x = g j (hi.trans hij) (f i j hij x))
    (m : ℕ) (hm : n ≤ m) (x : X m) :
    tailLift X f hf n g hg (of X f m x) = g m hm x := by
  change g (max n m) _ (f m (max n m) _ x) = g m hm x
  exact (hg m (max n m) hm (le_max_right _ _) x).symm

def ExtendsReals : Prop := ∀ n (g : C(X n,ℝ)),
  ∃ G : C(X (n+1),ℝ), ∀ x, G (f n (n+1) (Nat.le_succ n) x) = g x

variable (hext : ExtendsReals X f)

def realExtension (n : ℕ) (g : C(X n,ℝ)) : C(X (n+1),ℝ) := (hext n g).choose

omit [DirectedSystem X (f · · ·)] in
lemma realExtension_spec (n : ℕ) (g : C(X n,ℝ)) (x : X n) :
    realExtension X f hext n g (f n (n+1) (Nat.le_succ n) x) = g x :=
  (hext n g).choose_spec x

def realFamily (n : ℕ) (g : C(X n,ℝ)) (m : ℕ) (hm : n ≤ m) : C(X m,ℝ) :=
  Nat.leRecOn hm (fun {k} => realExtension X f hext k) g

omit [DirectedSystem X (f · · ·)] in
lemma realFamily_self (n : ℕ) (g : C(X n,ℝ)) : realFamily X f hext n g n le_rfl = g :=
  by simp only [realFamily,Nat.leRecOn_self]

lemma realFamily_compat (n : ℕ) (g : C(X n,ℝ)) (i j : ℕ) (hi : n ≤ i)
    (hij : i ≤ j) (x : X i) :
    realFamily X f hext n g i hi x =
      realFamily X f hext n g j (hi.trans hij) (f i j hij x) := by
  induction j,hij using Nat.le_induction with
  | base => rw [DirectedSystem.map_self']
  | succ j hij ih =>
    unfold realFamily
    rw [Nat.leRecOn_succ (hi.trans hij)]
    rw [← DirectedSystem.map_map' f hij (Nat.le_succ j),realExtension_spec]
    exact ih

include hf hext in
lemma exists_global_real_extension (n : ℕ) (g : C(X n,ℝ)) :
    ∃ G : C(Space X f,ℝ), ∀ x, G (of X f n x) = g x := by
  refine ⟨tailLift X f hf n (realFamily X f hext n g)
    (realFamily_compat X f hext n g),?_⟩
  intro x
  rw [tailLift_of X f hf n _ _ n le_rfl,realFamily_self]

include hf hext in
lemma t2Space (hsep : ∀ n (x y : X n), x ≠ y →
    ∃ g : C(X n,ℝ), g x ≠ g y) : T2Space (Space X f) := by
  constructor
  intro z w hzw
  obtain ⟨n,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ f z w
  have hxy : x ≠ y := fun h => hzw (congrArg (of X f n) h)
  obtain ⟨g,hg⟩ := hsep n x y hxy
  obtain ⟨G,hG⟩ := exists_global_real_extension X f hf hext n g
  apply separated_by_continuous G.continuous
  change G (of X f n x) ≠ G (of X f n y)
  rw [hG,hG]
  exact hg

lemma range_mono {i j : ℕ} (h : i ≤ j) : Set.range (of X f i) ⊆ Set.range (of X f j) := by
  rintro _ ⟨x,rfl⟩
  exact ⟨f i j h x,of_compat X f i j h x⟩

variable [∀ n, T1Space (X n)]

include hf in
lemma selection_closed (x : ℕ → Space X f) (hx : ∀ n, x n ∉ Set.range (of X f n))
    (S : Set (Space X f)) (hS : S ⊆ Set.range x) : IsClosed S := by
  rw [isClosed_iff]
  intro m
  have hfin : (S ∩ Set.range (of X f m)).Finite := by
    apply ((Set.finite_Iio m).image x).subset
    rintro z ⟨hzS,hzm⟩
    obtain ⟨n,rfl⟩ := hS hzS
    refine ⟨n,?_,rfl⟩
    change n < m
    by_contra hnm
    exact hx n (range_mono X f (Nat.le_of_not_gt hnm) hzm)
  have hh := hfin.preimage (of_injective X f hf m).injOn
  rw [Set.preimage_inter,Set.preimage_range,Set.inter_univ] at hh
  exact hh.isClosed

include hf in

theorem compact_bounded {K : Set (Space X f)} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (of X f n) := by
  classical
  by_contra hn
  have hex : ∀ n, ∃ x ∈ K, x ∉ Set.range (of X f n) := by
    intro n
    exact Set.not_subset.mp (fun h => hn ⟨n,h⟩)
  choose x hxK hx using hex
  have hall : ∀ S ⊆ Set.range x, IsClosed S := selection_closed X f hf x hx
  have hcompact : IsCompact (Set.range x) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hxK)
  have hdiscrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hfinite := hcompact.finite hdiscrete
  have hex : ∀ z ∈ Set.range x, ∃ n, z ∈ Set.range (of X f n) := by
    intro z _
    obtain ⟨n,y,rfl⟩ := DirectLimit.exists_eq_mk f z
    exact ⟨n,y,rfl⟩
  choose idx hidx using hex
  let n := hfinite.toFinset.sup (fun z => if hz : z ∈ Set.range x then idx z hz else 0)
  have hbound : Set.range x ⊆ Set.range (of X f n) := by
    intro z hz
    apply range_mono X f (j := n) _ (hidx z hz)
    have hh := Finset.le_sup (f := fun z => if hz : z ∈ Set.range x then idx z hz else 0)
      (hfinite.mem_toFinset.mpr hz)
    simpa only [dite_eq_left hz] using hh
  exact hx n (hbound (Set.mem_range_self n))

end UniversalFInfinity.TopologicalTower

namespace UniversalFInfinity.CellularTower
open Set Metric Topology
universe u
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable [∀ n, Nonempty (X n)]
variable [∀ n, CWComplex (Set.univ : Set (X n))]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

structure CellSystem where
  index : ℕ → Type u
  cell : ∀ n m, m ≤ n → index m → RelCWComplex.cell (Set.univ : Set (X n)) m
  injective : ∀ n m h, Function.Injective (cell n m h)
  exhaustive : ∀ n m (j : RelCWComplex.cell (Set.univ : Set (X n)) m),
    ∃ (h : m ≤ n) (i : index m), cell n m h i = j
  compatibility : ∀ n k (h : n ≤ k) (m : ℕ) (hm : m ≤ n) (i : index m) (x : Fin m → ℝ),
    f n k h (RelCWComplex.map m (cell n m hm i) x) =
      RelCWComplex.map m (cell k m (hm.trans h) i) x

variable (D : CellSystem X f)

abbrev Limit := TopologicalTower.Space X f
abbrev stage (n : ℕ) := TopologicalTower.of X f n

def map (m : ℕ) (i : D.index m) : PartialEquiv (Fin m → ℝ) (Limit X f) :=
  Cellular.transportedMap (TopologicalTower.of_closedEmbedding X f hf m)
    m (D.cell m m le_rfl i)

lemma map_eq_stage (n m : ℕ) (hm : m ≤ n) (i : D.index m) (x : Fin m → ℝ) :
    map X f hf D m i x = stage X f n (RelCWComplex.map m (D.cell n m hm i) x) := by
  change stage X f m (RelCWComplex.map m (D.cell m m le_rfl i) x) = _
  unfold stage
  rw [← TopologicalTower.of_compat X f m n hm,D.compatibility]

lemma map_image (n m : ℕ) (hm : m ≤ n) (i : D.index m) (S : Set (Fin m → ℝ)) :
    map X f hf D m i '' S = stage X f n '' (RelCWComplex.map m (D.cell n m hm i) '' S) := by
  rw [← Set.image_comp]
  congr 1
  funext x
  exact map_eq_stage X f hf D n m hm i x

def globalIndex (n m : ℕ) (j : RelCWComplex.cell (Set.univ : Set (X n)) m) : D.index m :=
  (D.exhaustive n m j).choose_spec.choose

omit [∀ n, Nonempty (X n)] [DirectedSystem X (f · · ·)] in
lemma globalIndex_spec (n m : ℕ) (j : RelCWComplex.cell (Set.univ : Set (X n)) m) :
    D.cell n m (D.exhaustive n m j).choose (globalIndex X f D n m j) = j :=
  (D.exhaustive n m j).choose_spec.choose_spec

lemma old_image (n m : ℕ) (j : RelCWComplex.cell (Set.univ : Set (X n)) m)
    (S : Set (Fin m → ℝ)) :
    stage X f n '' (RelCWComplex.map m j '' S) =
      map X f hf D m (globalIndex X f D n m j) '' S := by
  rw [map_image X f hf D n m (D.exhaustive n m j).choose,globalIndex_spec]

variable [∀ n, T2Space (X n)]

@[instance_reducible]
def cwComplex : CWComplex (Set.univ : Set (Limit X f)) where
  cell := D.index
  map := map X f hf D
  source_eq := fun m i => Cellular.transportedMap_source _ _ _
  continuousOn := fun m i => Cellular.transportedMap_continuousOn _ _ _
  continuousOn_symm := fun m i => Cellular.transportedMap_continuousOn_symm _ _ _
  pairwiseDisjoint' := by
    rintro ⟨m,i⟩ _ ⟨k,j⟩ _ hne
    change Disjoint (map X f hf D m i '' ball 0 1) (map X f hf D k j '' ball 0 1)
    rw [map_image X f hf D (max m k) m (le_max_left _ _),
      map_image X f hf D (max m k) k (le_max_right _ _)]
    apply (CWComplex.disjoint_openCell_of_ne ?_).image
      (TopologicalTower.of_injective X f hf (max m k)).injOn (Set.subset_univ _) (Set.subset_univ _)
    intro heq
    have hmk := congrArg Sigma.fst heq
    change m = k at hmk
    subst k
    have hij : D.cell (max m m) m (le_max_left _ _) i =
        D.cell (max m m) m (le_max_right _ _) j := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have : i = j := D.injective _ _ _ hij
    exact hne (by subst j; rfl)
  mapsTo' := by
    classical
    intro m i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell m (D.cell m m le_rfl i)
    refine ⟨fun k => (I k).image (globalIndex X f D m k),?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map m (D.cell m m le_rfl i) x ∈
      CWComplex.cellFrontier m (D.cell m m le_rfl i) from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨k,hkm,j,hj,hx'⟩ := h
    refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkm,Set.mem_iUnion.mpr
      ⟨globalIndex X f D m k j,Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [← old_image X f hf D m k j]
    exact ⟨_,hx',rfl⟩
  closed' := by
    intro A _ hA
    rw [TopologicalTower.isClosed_iff]
    intro n
    apply (CWComplex.closed Set.univ (stage X f n ⁻¹' A) (Set.subset_univ _)).mpr
    intro m j
    have h := (hA m (globalIndex X f D n m j)).preimage (TopologicalTower.continuous_of X f n)
    rw [← old_image X f hf D n m j,Set.preimage_inter,
      Set.preimage_image_eq _ (TopologicalTower.of_injective X f hf n)] at h
    exact h
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    have hx : x ∈ (Set.univ : Set (X n)) := Set.mem_univ _
    rw [← CWComplex.union (C := (Set.univ : Set (X n)))] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨m,j,hx⟩ := hx
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨globalIndex X f D n m j,?_⟩⟩
    rw [← old_image X f hf D n m j]
    exact ⟨x,hx,rfl⟩

lemma finite_cells (hfin : ∀ n, Finite (D.index n)) (n : ℕ) :
    Finite ((cwComplex X f hf D).cell n) := hfin n

end UniversalFInfinity.CellularTower

namespace UniversalFInfinity.Sequential
open Set Topology
universe u
variable (X : ℕ → Type u) [∀ n,TopologicalSpace (X n)]
variable (step : ∀ n,C(X n,X (n+1)))

def map (i j : ℕ) (h : i ≤ j) : C(X i,X j) :=
  Nat.leRecOn h (fun {k} F => (step k).comp F) (.id (X i))

@[simp] lemma map_self (i : ℕ) : map X step i i le_rfl = .id _ := by
  simp only [map,Nat.leRecOn_self]
lemma map_succ (i j : ℕ) (h : i ≤ j) :
    map X step i (j+1) (h.trans (Nat.le_succ j)) = (step j).comp (map X step i j h) := by
  simp only [map,Nat.leRecOn_succ h]
@[simp] lemma map_step (i : ℕ) : map X step i (i+1) (Nat.le_succ i) = step i := by
  rw [map_succ X step i i le_rfl,map_self,ContinuousMap.comp_id]

instance : DirectedSystem X (map X step · · ·) where
  map_self {i} x := by simp only [map_self,ContinuousMap.id_apply]
  map_map {k j i} hij hjk x := by
    induction k,hjk using Nat.le_induction with
    | base => simp only [map_self,ContinuousMap.id_apply]
    | succ k hk ih =>
      rw [map_succ X step j k hk,map_succ X step i k (hij.trans hk)]
      change step k (map X step j k hk (map X step i j hij x)) = step k (map X step i k (hij.trans hk) x)
      rw [ih]

lemma map_closedEmbedding (hs : ∀ n,IsClosedEmbedding (step n)) (i j : ℕ) (h : i ≤ j) :
    IsClosedEmbedding (map X step i j h) := by
  induction j,h using Nat.le_induction with
  | base => simpa only [map_self,ContinuousMap.coe_id] using IsClosedEmbedding.id
  | succ j h ih => rw [map_succ X step i j h]; exact (hs j).comp ih

variable [∀ n,CWComplex (univ : Set (X n))]

structure CellSteps where
  cell : ∀ n m,RelCWComplex.cell (univ : Set (X n)) m → RelCWComplex.cell (univ : Set (X (n+1))) m
  injective : ∀ n m,Function.Injective (cell n m)
  dim : ∀ n m (_ : RelCWComplex.cell (univ : Set (X n)) m),m ≤ n
  exhaustive : ∀ n m,m ≠ n+1 → ∀ j, ∃ i,cell n m i = j
  compatibility : ∀ n m i x,step n (RelCWComplex.map m i x) = RelCWComplex.map m (cell n m i) x

variable (D : CellSteps X step)
def cellMap (i j : ℕ) (h : i ≤ j) (m : ℕ) :
    RelCWComplex.cell (univ : Set (X i)) m → RelCWComplex.cell (univ : Set (X j)) m :=
  Nat.leRecOn h (fun {k} F => D.cell k m ∘ F) id

lemma cellMap_self (i m : ℕ) : cellMap X step D i i le_rfl m = id := by
  simp only [cellMap,Nat.leRecOn_self]
lemma cellMap_succ (i j : ℕ) (h : i ≤ j) (m : ℕ) :
    cellMap X step D i (j+1) (h.trans (Nat.le_succ j)) m = D.cell j m ∘ cellMap X step D i j h m := by
  simp only [cellMap,Nat.leRecOn_succ h]
lemma cellMap_injective (i j : ℕ) (h : i ≤ j) (m : ℕ) :
    Function.Injective (cellMap X step D i j h m) := by
  induction j,h using Nat.le_induction with
  | base => rw [cellMap_self]; exact Function.injective_id
  | succ j h ih => rw [cellMap_succ X step D i j h]; exact (D.injective j m).comp ih
lemma cellMap_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (m : ℕ) (c) :
    cellMap X step D j k hjk m (cellMap X step D i j hij m c) =
      cellMap X step D i k (hij.trans hjk) m c := by
  induction k,hjk using Nat.le_induction with
  | base => rw [cellMap_self]; rfl
  | succ k hk ih =>
    rw [cellMap_succ X step D j k hk,cellMap_succ X step D i k (hij.trans hk)]
    exact congrArg (D.cell k m) ih
lemma cellMap_compat (i j : ℕ) (h : i ≤ j) (m : ℕ) (c) (x : Fin m → ℝ) :
    map X step i j h (RelCWComplex.map m c x) = RelCWComplex.map m (cellMap X step D i j h m c) x := by
  induction j,h using Nat.le_induction with
  | base => rw [map_self,cellMap_self]; rfl
  | succ j h ih =>
    rw [map_succ X step i j h,cellMap_succ X step D i j h]
    change step j (map X step i j h (RelCWComplex.map m c x)) = _
    rw [ih,D.compatibility]

lemma cellMap_exhaustive (n m : ℕ) (c : RelCWComplex.cell (univ : Set (X n)) m) :
    ∃ (h : m ≤ n) (i : RelCWComplex.cell (univ : Set (X m)) m),cellMap X step D m n h m i = c := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero (D.dim 0 m c)
    subst m
    exact ⟨le_rfl,c,by rw [cellMap_self]; rfl⟩
  | succ n ih =>
    by_cases hm : m = n+1
    · subst m
      exact ⟨le_rfl,c,by rw [cellMap_self]; rfl⟩
    · obtain ⟨j,rfl⟩ := D.exhaustive n m hm c
      obtain ⟨h,i,hi⟩ := ih j
      refine ⟨h.trans (Nat.le_succ n),i,?_⟩
      rw [cellMap_succ X step D m n h]
      exact congrArg (D.cell n m) hi

variable [∀ n,Nonempty (X n)]
def cellSystem : CellularTower.CellSystem X (map X step) where
  index m := RelCWComplex.cell (univ : Set (X m)) m
  cell n m h := cellMap X step D m n h m
  injective n m h := cellMap_injective X step D m n h m
  exhaustive := cellMap_exhaustive X step D
  compatibility n k h m hm i x := by
    rw [cellMap_compat X step D n k h,cellMap_comp X step D m n k hm h]
end UniversalFInfinity.Sequential

end

end OAI
