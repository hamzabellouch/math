import OAI.GroupTheory.UniversalGroup.HomotopyProducts

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Attachment
noncomputable section
universe u v w
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev OpenDisk (n : ℕ) := ball (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩
def interior (n : ℕ) : OpenDisk n → Disk n :=
  fun x => ⟨x.1, ball_subset_closedBall x.2⟩
lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _
lemma continuous_interior (n : ℕ) : Continuous (interior n) :=
  continuous_subtype_val.subtype_mk _
lemma boundary_closedEmbedding (n : ℕ) : IsClosedEmbedding (boundary n) :=
  (continuous_boundary n).isClosedEmbedding (fun _ _ h => Subtype.ext (congrArg (fun z : Disk n => z.1) h))

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def Space (_a : ι → C(Sphere n,X)) := X ⊕ (Σ _ : ι, OpenDisk n)

noncomputable def quotient : (X ⊕ (Σ _ : ι, Disk n)) → Space a := by
  classical
  intro z
  cases z with
  | inl x => exact Sum.inl x
  | inr p =>
    exact if h : p.2.1 ∈ ball (0 : Fin n → ℝ) 1 then Sum.inr ⟨p.1,⟨p.2.1,h⟩⟩
    else Sum.inl (a p.1 ⟨p.2.1,by
      have hd := p.2.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hd (le_of_not_gt h)⟩)

instance : TopologicalSpace (Space a) := TopologicalSpace.coinduced (quotient a) inferInstance

@[simp] lemma quotient_inl (x : X) : quotient a (Sum.inl x) = Sum.inl x := rfl

@[simp] lemma quotient_interior (i : ι) (x : OpenDisk n) :
    quotient a (Sum.inr ⟨i,interior n x⟩) = Sum.inr ⟨i,x⟩ := by
  classical
  exact dite_eq_left x.2

@[simp] lemma quotient_boundary (i : ι) (x : Sphere n) :
    quotient a (Sum.inr ⟨i,boundary n x⟩) = Sum.inl (a i x) := by
  classical
  have hx : x.1 ∉ ball (0 : Fin n → ℝ) 1 := by
    simpa only [mem_ball,mem_sphere,x.2,lt_self_iff_false,not_false_eq_true] using
      (sphere_disjoint_ball.notMem_of_mem_left x.2)
  exact dite_eq_right hx

lemma quotient_surjective : Function.Surjective (quotient a) := by
  intro z
  cases z with
  | inl x => exact ⟨Sum.inl x,rfl⟩
  | inr p => exact ⟨Sum.inr ⟨p.1,interior n p.2⟩,quotient_interior a p.1 p.2⟩

lemma continuous_quotient : Continuous (quotient a) := continuous_coinduced_rng

def base : X → Space a := Sum.inl
noncomputable def cell (i : ι) : C(Disk n,Space a) :=
  ⟨fun x => quotient a (Sum.inr ⟨i,x⟩),
    (continuous_quotient a).comp (continuous_inr.comp continuous_sigmaMk)⟩
lemma continuous_base : Continuous (base a) :=
  (continuous_quotient a).comp continuous_inl

@[simp] lemma cell_boundary (i : ι) (x : Sphere n) :
    cell a i (boundary n x) = base a (a i x) := quotient_boundary a i x
@[simp] lemma cell_interior (i : ι) (x : OpenDisk n) :
    cell a i (interior n x) = Sum.inr ⟨i,x⟩ := quotient_interior a i x

lemma continuous_iff {Y : Type w} [TopologicalSpace Y] (f : Space a → Y) :
    Continuous f ↔ Continuous (f ∘ base a) ∧ ∀ i, Continuous (f ∘ cell a i) := by
  change Continuous[TopologicalSpace.coinduced (quotient a) inferInstance,_] f ↔ _
  rw [continuous_coinduced_dom,continuous_sum_dom,continuous_sigma_iff]
  rfl

lemma isClosed_iff (S : Set (Space a)) :
    IsClosed S ↔ IsClosed (base a ⁻¹' S) ∧ ∀ i, IsClosed (cell a i ⁻¹' S) := by
  change @IsClosed _ (TopologicalSpace.coinduced (quotient a) inferInstance) S ↔ _
  rw [isClosed_coinduced,isClosed_sum_iff,isClosed_sigma_iff]
  rfl

lemma cell_preimage_base_image (i : ι) (S : Set X) :
    cell a i ⁻¹' (base a '' S) = boundary n '' ((a i) ⁻¹' S) := by
  classical
  ext d
  by_cases h : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have hd : d = interior n ⟨d.1,h⟩ := rfl
    rw [hd]
    simp only [Set.mem_preimage,cell_interior,base,Set.mem_image]
    constructor
    · rintro ⟨x,_,hx⟩; cases hx
    · rintro ⟨x,_,hx⟩
      have heq := congrArg (fun d : Disk n => d.1) hx
      have hh : x.1 ∈ ball (0 : Fin n → ℝ) 1 := heq ▸ h
      exact False.elim ((sphere_disjoint_ball.notMem_of_mem_left x.2) hh)
  · let x : Sphere n := ⟨d.1,by
      have hd := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hd (le_of_not_gt h)⟩
    have hd : d = boundary n x := rfl
    rw [hd]
    simp only [Set.mem_preimage,cell_boundary,Set.mem_image]
    constructor
    · rintro ⟨y,hy,hyx⟩
      have heq : y = a i x := Sum.inl_injective hyx
      exact ⟨x,heq ▸ hy,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      have heq : y = x := Subtype.ext (congrArg (fun d : Disk n => d.1) hyx)
      subst y
      exact ⟨a i x,hy,rfl⟩

lemma base_isClosedMap : IsClosedMap (base a) := by
  intro S hS
  rw [isClosed_iff]
  constructor
  · have heq : base a ⁻¹' (base a '' S) = S :=
      Set.preimage_image_eq S Sum.inl_injective
    exact heq.symm ▸ hS
  · intro i
    rw [cell_preimage_base_image]
    exact (boundary_closedEmbedding n).isClosedMap _ (hS.preimage (a i).continuous)

lemma base_closedEmbedding : IsClosedEmbedding (base a) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_base a) Sum.inl_injective (base_isClosedMap a)

noncomputable def lift {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x)) : C(Space a,Y) := by
  classical
  let F : Space a → Y := Sum.elim f (fun p => g p.1 (interior n p.2))
  have hcell (i : ι) : F ∘ cell a i = g i := by
    funext d
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d = interior n ⟨d.1,hd⟩ := rfl
      rw [heq,Function.comp_apply,cell_interior]
      rfl
    · let x : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have heq : d = boundary n x := rfl
      rw [heq,Function.comp_apply,cell_boundary]
      exact (h i x).symm
  exact ⟨F,(continuous_iff a F).mpr ⟨f.continuous,fun i => by rw [hcell]; exact (g i).continuous⟩⟩

@[simp] lemma lift_base {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x)) (x : X) :
    lift a f g h (base a x) = f x := rfl

@[simp] lemma lift_cell {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x))
    (i : ι) (d : Disk n) : lift a f g h (cell a i d) = g i d := by
  classical
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq,cell_interior]
    rfl
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    rw [heq,cell_boundary,lift_base,h]

lemma lift_unique {Y : Type w} [TopologicalSpace Y] (f g : C(Space a,Y))
    (hb : ∀ x, f (base a x) = g (base a x))
    (hc : ∀ i d, f (cell a i d) = g (cell a i d)) : f = g := by
  ext z
  obtain ⟨q,rfl⟩ := quotient_surjective a z
  cases q with
  | inl x => exact hb x
  | inr p => exact hc p.1 p.2

lemma interior_openEmbedding (n : ℕ) : IsOpenEmbedding (interior n) :=
  .inclusion ball_subset_closedBall (isOpen_ball.preimage continuous_subtype_val)

def openCell (i : ι) : OpenDisk n → Space a := fun x => Sum.inr ⟨i,x⟩

lemma openCell_eq (i : ι) : openCell a i = cell a i ∘ interior n := by
  funext x
  exact (cell_interior a i x).symm

lemma quotient_preimage_openCell_image (i : ι) (S : Set (OpenDisk n)) :
    quotient a ⁻¹' (openCell a i '' S) =
      Sum.inr '' (Sigma.mk i '' (interior n '' S)) := by
  classical
  ext q
  cases q with
  | inl x =>
    simp only [Set.mem_preimage,quotient_inl,Set.mem_image]
    constructor
    · rintro ⟨y,_,hy⟩; cases hy
    · rintro ⟨y,_,hy⟩; cases hy
  | inr p =>
    by_cases hp : p.2.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : p.2 = interior n ⟨p.2.1,hp⟩ := rfl
      change (∃ x ∈ S, openCell a i x = quotient a (Sum.inr ⟨p.1,p.2⟩)) ↔ _
      rw [heq,quotient_interior]
      constructor
      · rintro ⟨x,hx,he⟩
        have hh : (⟨i,x⟩ : Σ _ : ι, OpenDisk n) = ⟨p.1,⟨p.2.1,hp⟩⟩ := Sum.inr_injective he
        have hh' : (⟨i,interior n x⟩ : Σ _ : ι, Disk n) = ⟨p.1,p.2⟩ :=
          congrArg (fun p : Σ _ : ι, OpenDisk n => (⟨p.1,interior n p.2⟩ : Σ _ : ι, Disk n)) hh
        exact ⟨⟨i,interior n x⟩,⟨interior n x,⟨x,hx,rfl⟩,rfl⟩,congrArg Sum.inr hh'⟩
      · rintro ⟨y,⟨d,⟨x,hx,hxd⟩,hdy⟩,hy⟩
        subst d; subst y
        have hh := Sum.inr_injective hy
        have hi : i = p.1 := congrArg Sigma.fst hh
        subst i
        have hh' : interior n x = interior n ⟨p.2.1,hp⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
        have he : x = ⟨p.2.1,hp⟩ := (interior_openEmbedding n).injective hh'
        exact ⟨x,hx,by subst x; rfl⟩
    · let x : Sphere n := ⟨p.2.1,by
        have hm := p.2.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hp)⟩
      have heq : p.2 = boundary n x := rfl
      change (∃ y ∈ S, openCell a i y = quotient a (Sum.inr ⟨p.1,p.2⟩)) ↔ _
      rw [heq,quotient_boundary]
      constructor
      · rintro ⟨y,_,hy⟩; cases hy
      · rintro ⟨y,⟨d,⟨z,_,hzd⟩,hdy⟩,hy⟩
        subst d; subst y
        have hh := Sum.inr_injective hy
        have hi : i = p.1 := congrArg Sigma.fst hh
        subst i
        have hh' : interior n z = boundary n x := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
        have hh'' := congrArg (fun d : Disk n => d.1) hh'
        exact False.elim (hp (hh'' ▸ z.2))

lemma openCell_openEmbedding (i : ι) : IsOpenEmbedding (openCell a i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · rw [openCell_eq]
    exact (cell a i).continuous.comp (continuous_interior n)
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  · intro S hS
    change @IsOpen _ (TopologicalSpace.coinduced (quotient a) inferInstance) _
    rw [isOpen_coinduced,quotient_preimage_openCell_image]
    exact isOpenMap_inr _ (isOpenMap_sigmaMk _ ((interior_openEmbedding n).isOpenMap S hS))

lemma exists_real_extension (f : C(X,ℝ)) :
    ∃ F : C(Space a,ℝ), ∀ x, F (base a x) = f x := by
  classical
  have hi (i : ι) : ∃ g : C(Disk n,ℝ), ∀ x, g (boundary n x) = f (a i x) := by
    obtain ⟨g,hg⟩ := (f.comp (a i)).exists_extension' (boundary_closedEmbedding n)
    exact ⟨g,fun x => congrFun hg x⟩
  choose g hg using hi
  exact ⟨lift a f g hg,fun x => lift_base a f g hg x⟩

def RealSeparated (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ x y : Y, x ≠ y → ∃ f : C(Y,ℝ), f x ≠ f y

lemma RealSeparated.t2Space {Y : Type*} [TopologicalSpace Y] (h : RealSeparated Y) :
    T2Space Y := by
  constructor
  intro x y hxy
  obtain ⟨f,hf⟩ := h x y hxy
  exact separated_by_continuous f.continuous hf

lemma realSeparated_of_tychonoff {Y : Type*} [TopologicalSpace Y]
    [T1Space Y] [CompletelyRegularSpace Y] : RealSeparated Y := by
  intro x y hxy
  obtain ⟨f,hf,hfx,hfy⟩ := CompletelyRegularSpace.completely_regular x {y} isClosed_singleton
    (by simpa only [Set.mem_singleton_iff] using hxy)
  refine ⟨⟨fun q => (f q : ℝ),continuous_subtype_val.comp hf⟩,?_⟩
  change (f x : ℝ) ≠ (f y : ℝ)
  rw [hfx,hfy (Set.mem_singleton y)]
  norm_num

lemma exists_interior_separator [T1Space X] (i : ι) (x : OpenDisk n) (z : Space a)
    (hxz : openCell a i x ≠ z) :
    ∃ F : C(Space a,ℝ), F (openCell a i x) = 1 ∧ F z = 0 := by
  classical
  let K : Set (Disk n) := Set.range (boundary n) ∪ cell a i ⁻¹' {z}
  have hKc : IsClosed K := by

    have hz : IsClosed (cell a i ⁻¹' {z}) := by
      cases z with
      | inl y =>
        have heq : ({base a y} : Set (Space a)) = base a '' {y} :=
          Set.image_singleton.symm
        change IsClosed (cell a i ⁻¹' {base a y})
        rw [heq,cell_preimage_base_image]

        exact (boundary_closedEmbedding n).isClosedMap _
          (isClosed_singleton.preimage (a i).continuous)
      | inr p =>
        have heq : ({openCell a p.1 p.2} : Set (Space a)) = openCell a p.1 '' {p.2} :=
          Set.image_singleton.symm
        have hpre := quotient_preimage_openCell_image a p.1 ({p.2} : Set (OpenDisk n))
        have hclosed : IsClosed (quotient a ⁻¹' {Sum.inr p}) := by
          change IsClosed (quotient a ⁻¹' {openCell a p.1 p.2})
          rw [heq,hpre]
          exact isClosedMap_inr _ (isClosedMap_sigmaMk _
            ((isCompact_singleton.image (continuous_interior n)).isClosed))
        exact hclosed.preimage (continuous_inr.comp continuous_sigmaMk)
    exact (boundary_closedEmbedding n).isClosed_range.union hz
  have hxK : interior n x ∉ K := by
    rintro (hx | hx)
    · obtain ⟨s,hs⟩ := hx
      have heq := congrArg (fun d : Disk n => d.1) hs
      exact sphere_disjoint_ball.notMem_of_mem_left s.2 (heq ▸ x.2)
    · change cell a i (interior n x) = z at hx
      exact hxz ((cell_interior a i x).symm.trans hx)
  obtain ⟨f,hf0,hf1,_⟩ := exists_continuous_zero_one_of_isClosed hKc
    (isClosed_singleton (x := interior n x)) (Set.disjoint_singleton_right.mpr hxK)
  let g : ι → C(Disk n,ℝ) := fun j => if j = i then f else ContinuousMap.const _ 0
  have hgb (j : ι) (s : Sphere n) : g j (boundary n s) = (0 : ℝ) := by
    dsimp [g]
    split_ifs with hji
    · exact hf0 (Set.mem_union_left _ (Set.mem_range_self s))
    · rfl
  let F : C(Space a,ℝ) := lift a (ContinuousMap.const _ 0) g hgb
  have hFcell (j : ι) (d : Disk n) : F (cell a j d) = g j d := lift_cell a _ _ _ j d
  refine ⟨F,?_,?_⟩
  · change F (Sum.inr ⟨i,x⟩) = 1
    rw [← cell_interior a i x,hFcell]
    simpa only [g,ite_eq_left rfl,Pi.one_apply] using hf1 (Set.mem_singleton _)
  · cases z with
    | inl y => exact lift_base a _ _ _ y
    | inr p =>
      rw [← cell_interior a p.1 p.2,hFcell]
      by_cases hpi : p.1 = i
      · have hm : interior n p.2 ∈ K := by
          right
          change cell a i (interior n p.2) = Sum.inr p
          rw [cell_interior]
          cases p with
          | mk j y => cases hpi; rfl
        simpa only [g,ite_eq_left hpi,Pi.zero_apply] using hf0 hm
      · simp only [g,ite_eq_right hpi,ContinuousMap.const_apply]

lemma realSeparated (hX : RealSeparated X) : RealSeparated (Space a) := by
  classical
  let : T2Space X := hX.t2Space
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hne : x ≠ y := fun heq => hxy (congrArg Sum.inl heq)
      obtain ⟨f,hf⟩ := hX x y hne
      obtain ⟨F,hF⟩ := exists_real_extension a f
      refine ⟨F,?_⟩
      change F (base a x) ≠ F (base a y)
      rwa [hF,hF]
    | inr p =>
      obtain ⟨F,hF1,hF0⟩ := exists_interior_separator a p.1 p.2 (Sum.inl x)
        (by exact fun h => hxy h.symm)
      refine ⟨F,?_⟩
      change F (Sum.inl x) ≠ F (openCell a p.1 p.2)
      rw [hF0,hF1]
      norm_num
  | inr p =>
    obtain ⟨F,hF1,hF0⟩ := exists_interior_separator a p.1 p.2 y hxy
    refine ⟨F,?_⟩
    change F (openCell a p.1 p.2) ≠ F y
    rw [hF1,hF0]
    norm_num

lemma t2Space (hX : RealSeparated X) : T2Space (Space a) := (realSeparated a hX).t2Space

section Characteristic
variable [Nonempty X]

def characteristic (i : ι) (x : Fin n → ℝ) : Space a := by
  classical
  exact if hx : x ∈ closedBall 0 1 then cell a i ⟨x,hx⟩ else base a (Classical.choice ‹Nonempty X›)

lemma characteristic_disk (i : ι) (d : Disk n) :
    characteristic a i d.1 = cell a i d := by
  simp only [characteristic,dite_eq_left d.2]

lemma characteristic_open (i : ι) (x : OpenDisk n) :
    characteristic a i x.1 = openCell a i x := by
  exact (characteristic_disk a i (interior n x)).trans (cell_interior a i x)

lemma characteristic_bijOn (i : ι) :
    Set.BijOn (characteristic a i) (ball 0 1) (Set.range (openCell a i)) := by
  constructor
  · intro x hx
    exact ⟨⟨x,hx⟩,(characteristic_open a i ⟨x,hx⟩).symm⟩
  constructor
  · intro x hx y hy hxy
    have hxy' : openCell a i ⟨x,hx⟩ = openCell a i ⟨y,hy⟩ := by
      rwa [characteristic_open a i ⟨x,hx⟩,characteristic_open a i ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val ((openCell_openEmbedding a i).injective hxy')
  · rintro z ⟨x,rfl⟩
    exact ⟨x.1,x.2,characteristic_open a i x⟩

def characteristicPE (i : ι) : PartialEquiv (Fin n → ℝ) (Space a) :=
  (characteristic_bijOn a i).toPartialEquiv _ _ _

lemma characteristicPE_continuousOn (i : ι) :
    ContinuousOn (characteristicPE a i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (closedBall (0:Fin n→ℝ) 1).domRestrict (characteristicPE a i) = cell a i := by
    funext x
    exact characteristic_disk a i x
  rw [heq]
  exact (cell a i).continuous

lemma characteristicPE_continuousOn_symm (i : ι) :
    ContinuousOn (characteristicPE a i).symm (characteristicPE a i).target := by
  let e := characteristicPE a i
  have he : IsEmbedding (e.source.domRestrict e) := by
    have heq : e.source.domRestrict e = openCell a i := by
      funext x
      exact characteristic_open a i x
    rw [heq]
    exact (openCell_openEmbedding a i).isEmbedding
  let H : e.source ≃ₜ e.target := e.toEquiv.toHomeomorphOfIsInducing
    (he.isInducing.codRestrict (fun x => e.map_source x.2))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp H.symm.continuous

lemma characteristicPE_image_ball (i : ι) :
    characteristicPE a i '' ball 0 1 = Set.range (openCell a i) :=
  (characteristic_bijOn a i).image_eq

lemma characteristicPE_image_closedBall (i : ι) :
    characteristicPE a i '' closedBall 0 1 = Set.range (cell a i) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,(characteristic_disk a i ⟨x,hx⟩).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,x.2,characteristic_disk a i x⟩

abbrev CellIndex (m n : ℕ) (ι : Type v) := ULift.{u} (PLift (m = n) × ι)

def cellMap (m : ℕ) (i : CellIndex.{u,v} m n ι) :
    PartialEquiv (Fin m → ℝ) (Space a) := by
  obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
  subst m
  exact characteristicPE a i

@[instance_reducible]
def relCWComplex : RelCWComplex (Set.univ : Set (Space a)) (Set.range (base a)) where
  cell m := CellIndex.{u,v} m n ι
  map := cellMap a
  source_eq := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    rfl
  continuousOn := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    exact characteristicPE_continuousOn a i
  continuousOn_symm := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    exact characteristicPE_continuousOn_symm a i
  pairwiseDisjoint' := by
    rintro ⟨m,⟨⟨⟨hm⟩,i⟩⟩⟩ _ ⟨k,⟨⟨⟨hk⟩,j⟩⟩⟩ _ hne
    subst m; subst k
    change Disjoint (characteristicPE a i '' ball 0 1) (characteristicPE a j '' ball 0 1)
    rw [characteristicPE_image_ball,characteristicPE_image_ball]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,h⟩
    have hij : j = i := congrArg Sigma.fst (Sum.inr_injective h)
    subst j
    exact hne rfl
  disjointBase' := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    change Disjoint (characteristicPE a i '' ball 0 1) _
    rw [characteristicPE_image_ball]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,h⟩
    cases h
  mapsTo := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    refine ⟨fun _ => ∅,?_⟩
    intro x hx
    left
    refine ⟨a i ⟨x,hx⟩,?_⟩
    change base a (a i ⟨x,hx⟩) = characteristic a i x
    exact (cell_boundary a i ⟨x,hx⟩).symm.trans
      (characteristic_disk a i (boundary n ⟨x,hx⟩)).symm
  closed' := by
    intro A _ hA
    apply (isClosed_iff a A).mpr
    constructor
    · have h := hA.2.preimage (continuous_base a)
      convert h using 1
      ext x
      simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_range_self,and_true]
    · intro i
      have h := (hA.1 n ⟨⟨⟨rfl⟩,i⟩⟩).preimage (cell a i).continuous
      change IsClosed ((cell a i) ⁻¹' (A ∩ characteristicPE a i '' closedBall 0 1)) at h
      rw [characteristicPE_image_closedBall] at h
      convert h using 1
      ext x
      simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_range_self,and_true]
  isClosedBase := (base_closedEmbedding a).isClosed_range
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | inl x => exact Or.inl ⟨x,rfl⟩
    | inr p =>
      right
      refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨⟨⟨rfl⟩,p.1⟩⟩,?_⟩⟩
      change Sum.inr p ∈ characteristicPE a p.1 '' closedBall 0 1
      rw [characteristicPE_image_closedBall]
      exact ⟨interior n p.2,cell_interior a p.1 p.2⟩

end Characteristic

end
end UniversalFInfinity.Attachment

open Set Metric Topology

end OAI
