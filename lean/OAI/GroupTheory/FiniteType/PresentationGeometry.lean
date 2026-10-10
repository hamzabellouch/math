import Mathlib

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

theorem quotientMk_isClosedMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    IsClosedMap (Quotient.mk r) := by
  intro A hA
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have hs := isClosedMap_snd_of_compactSpace
    ({p : X × X | r p.1 p.2} ∩ Prod.fst ⁻¹' A) (hr.inter (hA.preimage continuous_fst))
  convert hs using 1
  ext x
  simp only [mem_preimage, mem_image, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨(a, x), ⟨Quotient.exact hx, ha⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨hab, ha⟩, rfl⟩
    exact ⟨a, ha, Quotient.sound hab⟩

theorem quotient_t2Space {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r : Setoid X) (hr : IsClosed {p : X × X | r p.1 p.2}) :
    T2Space (Quotient r) := by
  have hp : IsProperMap (Quotient.mk r) := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨continuous_quotient_mk', quotientMk_isClosedMap r hr, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
    have hc : IsClosed {a | r a x} := hr.preimage (continuous_id.prodMk continuous_const)
    convert hc.isCompact using 1
    ext a
    exact Quotient.eq
  apply t2_iff_isClosed_diagonal.mpr
  have h := (hp.prodMap hp).isClosedMap _ hr
  convert h using 1
  ext p
  simp only [mem_diagonal_iff, mem_image, mem_ofPred_eq]
  constructor
  · intro he
    obtain ⟨x, hx⟩ := Quotient.mk_surjective p.1
    exact ⟨(x, x), r.refl x, Prod.ext hx (hx.trans he)⟩
  · rintro ⟨⟨a, b⟩, hab, he⟩
    cases he
    exact Quotient.sound hab

namespace Adjunction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set Y}

noncomputable def normalize (f : C(A, X)) : X ⊕ Y → X ⊕ Y := by
  classical
  exact Sum.elim Sum.inl (fun y => if h : y ∈ A then Sum.inl (f ⟨y, h⟩) else Sum.inr y)

noncomputable def relation (f : C(A, X)) : Setoid (X ⊕ Y) :=
  Setoid.ker (normalize f)

@[simp] theorem relation_iff (f : C(A, X)) (a b : X ⊕ Y) :
    relation f a b ↔ normalize f a = normalize f b := Iff.rfl

abbrev Space (f : C(A, X)) := Quotient (relation f)

def old (f : C(A, X)) (x : X) : Space f := Quotient.mk _ (Sum.inl x)
def disk (f : C(A, X)) (y : Y) : Space f := Quotient.mk _ (Sum.inr y)

@[simp] theorem normalize_inl (f : C(A, X)) (x : X) :
    normalize f (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem normalize_inr_mem (f : C(A, X)) (y : A) :
    normalize f (Sum.inr y.1) = Sum.inl (f y) := by
  simp [normalize, y.property]

@[simp] theorem normalize_inr_notMem (f : C(A, X)) (y : Y) (hy : y ∉ A) :
    normalize f (Sum.inr y) = Sum.inr y := by
  simp [normalize, hy]

theorem relation_eq (f : C(A, X)) :
    {p : (X ⊕ Y) × (X ⊕ Y) | relation f p.1 p.2} =
    diagonal (X ⊕ Y) ∪
      range (fun a : A => (Sum.inl (f a), Sum.inr a.1)) ∪
      range (fun a : A => (Sum.inr a.1, Sum.inl (f a))) ∪
      (fun p : A × A => (Sum.inr p.1.1, Sum.inr p.2.1)) ''
        {p : A × A | f p.1 = f p.2} := by
  classical
  ext p
  rcases p with ⟨x | y, x' | y'⟩
  · simp [relation_iff, normalize]
  · by_cases hy : y' ∈ A
    · simp [relation_iff, normalize, hy, Subtype.exists, eq_comm]
    · simp [relation_iff, normalize, hy, Subtype.exists]
  · by_cases hy : y ∈ A
    · simp [relation_iff, normalize, hy, Subtype.exists]
    · simp [relation_iff, normalize, hy, Subtype.exists]
  · by_cases hy : y ∈ A <;> by_cases hy' : y' ∈ A
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]
      rintro rfl
      rfl
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]
      exact fun he => hy' (he ▸ hy)
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]
      exact fun he => hy (he.symm ▸ hy')
    · simp [relation_iff, normalize, hy, hy', Subtype.exists]

theorem relation_isClosed [T2Space X] [T2Space Y] [CompactSpace Y]
    (hA : IsClosed A) (f : C(A, X)) :
    IsClosed {p : (X ⊕ Y) × (X ⊕ Y) | relation f p.1 p.2} := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  rw [relation_eq]
  refine ((isClosed_diagonal.union ?_).union ?_).union ?_
  · exact (isCompact_range (continuous_inl.comp f.continuous |>.prodMk
      (continuous_inr.comp continuous_subtype_val))).isClosed
  · exact (isCompact_range (continuous_inr.comp continuous_subtype_val |>.prodMk
      (continuous_inl.comp f.continuous))).isClosed
  · apply IsCompact.isClosed
    apply IsCompact.image
      (isClosed_eq (f.continuous.comp continuous_fst) (f.continuous.comp continuous_snd)).isCompact
    fun_prop

theorem t2Space [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (hA : IsClosed A) (f : C(A, X)) : T2Space (Space f) :=
  quotient_t2Space (relation f) (relation_isClosed hA f)

theorem continuous_old (f : C(A, X)) : Continuous (old f) :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_disk (f : C(A, X)) : Continuous (disk f) :=
  continuous_quotient_mk'.comp continuous_inr

@[simp] theorem old_inj (f : C(A, X)) {x x' : X} : old f x = old f x' ↔ x = x' := by
  change Quotient.mk (relation f) (Sum.inl x) = Quotient.mk (relation f) (Sum.inl x') ↔ _
  rw [Quotient.eq]
  simp only [relation_iff, normalize_inl, Sum.inl.injEq]

@[simp] theorem disk_boundary (f : C(A, X)) (y : A) : disk f y.1 = old f (f y) := by
  apply Quotient.sound
  exact normalize_inr_mem f y

theorem old_isClosedEmbedding [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (hA : IsClosed A) (f : C(A, X)) : IsClosedEmbedding (old f) := by
  let := t2Space hA f
  exact (continuous_old f).isClosedEmbedding (fun _ _ => (old_inj f).mp)

def interiorMap (f : C(A, X)) (y : (Aᶜ : Set Y)) : Space f := disk f y.1

@[simp] theorem disk_eq_disk_of_notMem (f : C(A, X)) {y y' : Y} (hy : y ∉ A) :
    disk f y = disk f y' ↔ y = y' := by
  classical
  change Quotient.mk (relation f) _ = Quotient.mk (relation f) _ ↔ _
  rw [Quotient.eq, relation_iff, normalize_inr_notMem _ _ hy]
  by_cases hy' : y' ∈ A
  · simp only [normalize_inr_mem f ⟨y', hy'⟩, Sum.inr_ne_inl, false_iff]
    rintro rfl
    exact hy hy'
  · simp [normalize_inr_notMem _ _ hy']

@[simp] theorem old_ne_disk_of_notMem (f : C(A, X)) (x : X) {y : Y} (hy : y ∉ A) :
    old f x ≠ disk f y := by
  intro he
  have h : normalize f (Sum.inl x) = normalize f (Sum.inr y) := Quotient.exact he
  simp only [normalize_inl, normalize_inr_notMem _ _ hy, Sum.inl_ne_inr] at h

theorem interiorMap_preimage_image (f : C(A, X)) (U : Set (Aᶜ : Set Y)) :
    Quotient.mk (relation f) ⁻¹' (interiorMap f '' U) =
      (fun y : (Aᶜ : Set Y) => (Sum.inr y.1 : X ⊕ Y)) '' U := by
  ext z
  constructor
  · rintro ⟨y, hy, he⟩
    rcases z with x | z
    · exact False.elim (old_ne_disk_of_notMem f x y.property he.symm)
    · exact ⟨y, hy, congrArg Sum.inr ((disk_eq_disk_of_notMem f y.property).mp he)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem interiorMap_isOpenEmbedding (hA : IsClosed A) (f : C(A, X)) :
    IsOpenEmbedding (interiorMap f) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (continuous_disk f).comp continuous_subtype_val
  · intro a b he
    exact Subtype.ext ((disk_eq_disk_of_notMem f a.property).mp he)
  · intro U hU
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    change IsOpen (Quotient.mk (relation f) ⁻¹' (interiorMap f '' U))
    rw [interiorMap_preimage_image]
    exact (isOpenMap_inr.comp hA.isOpen_compl.isOpenMap_subtype_val) U hU

end Adjunction

namespace Cells
section

open Metric

abbrev Disk (d : ℕ) := (closedBall (0 : Fin d → ℝ) 1 : Set (Fin d → ℝ))
abbrev OpenDisk (d : ℕ) := (ball (0 : Fin d → ℝ) 1 : Set (Fin d → ℝ))

def boundary (k d : ℕ) : Set (Fin k × Disk d) :=
  {p | p.2.1 ∈ sphere (0 : Fin d → ℝ) 1}

theorem boundary_closed (k d : ℕ) : IsClosed (boundary k d) :=
  isClosed_sphere.preimage (continuous_subtype_val.comp continuous_snd)

variable {X : Type*} [TopologicalSpace X] {k d : ℕ}
variable (f : C(boundary k d, X))

abbrev Space := Adjunction.Space f

instance [T2Space X] [CompactSpace X] : T2Space (Space f) :=
  Adjunction.t2Space (boundary_closed k d) f

def characteristic (i : Fin k) (v : Fin d → ℝ) : Space f := by
  classical
  exact if h : v ∈ closedBall (0 : Fin d → ℝ) 1
    then Adjunction.disk f (i, ⟨v, h⟩)
    else Adjunction.disk f (i, ⟨0, by simp⟩)

@[simp] theorem characteristic_on_disk (i : Fin k) (v : Disk d) :
    characteristic f i v.1 = Adjunction.disk f (i, v) := by
  simp [characteristic, v.property]

theorem characteristic_continuousOn (i : Fin k) :
    ContinuousOn (characteristic f i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : ((closedBall 0 1).domRestrict (characteristic f i)) =
      fun v : Disk d => Adjunction.disk f (i, v) := by
    funext v
    exact characteristic_on_disk f i v
  rw [he]
  exact (Adjunction.continuous_disk f).comp (continuous_const.prodMk continuous_id)

def interiorInDisk (v : OpenDisk d) : Disk d := ⟨v.1, ball_subset_closedBall v.2⟩

theorem interiorInDisk_isOpenEmbedding : IsOpenEmbedding (interiorInDisk (d := d)) :=
  IsOpenEmbedding.id.restrict (fun _ h => ball_subset_closedBall h) isOpen_ball

def interiorInFamily (i : Fin k) (v : OpenDisk d) : ↑((boundary k d)ᶜ) :=
  ⟨(i, interiorInDisk v), by
    change v.1 ∉ sphere (0 : Fin d → ℝ) 1
    exact ne_of_lt v.2⟩

theorem prodMk_isOpenEmbedding (i : Fin k) :
    IsOpenEmbedding (Prod.mk i : Disk d → Fin k × Disk d) := by
  refine ⟨isEmbedding_prodMkRight i, ?_⟩
  have he : range (Prod.mk i : Disk d → Fin k × Disk d) = {i} ×ˢ univ := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨rfl, mem_univ _⟩
    · rintro ⟨hp, _⟩
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [he]
  exact (isOpen_discrete _).prod isOpen_univ

theorem interiorInFamily_isOpenEmbedding (i : Fin k) :
    IsOpenEmbedding (interiorInFamily (d := d) i) := by
  have hh : IsOpenEmbedding (fun v : OpenDisk d => (i, interiorInDisk v)) :=
    (prodMk_isOpenEmbedding i).comp interiorInDisk_isOpenEmbedding
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hh.continuous.subtype_mk _
  · intro a b h
    exact hh.injective (congrArg Subtype.val h)
  · exact hh.isOpenMap.subtype_mk _

theorem characteristic_interior (i : Fin k) :
    (OpenDisk d).domRestrict (characteristic f i) =
      Adjunction.interiorMap f ∘ interiorInFamily i := by
  funext v
  exact characteristic_on_disk f i (interiorInDisk v)

theorem characteristic_isOpenEmbedding (i : Fin k) :
    IsOpenEmbedding ((OpenDisk d).domRestrict (characteristic f i)) := by
  rw [characteristic_interior]
  exact (Adjunction.interiorMap_isOpenEmbedding (boundary_closed k d) f).comp
    (interiorInFamily_isOpenEmbedding i)

theorem characteristic_injOn (i : Fin k) :
    InjOn (characteristic f i) (ball 0 1) := by
  intro a ha b hb he
  exact congrArg Subtype.val ((characteristic_isOpenEmbedding f i).injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) he)

def chart (i : Fin k) : PartialEquiv (Fin d → ℝ) (Space f) :=
  (characteristic_injOn f i).toPartialEquiv (characteristic f i) (ball 0 1)

@[simp] theorem chart_coe (i : Fin k) : (chart f i : (Fin d → ℝ) → Space f) =
    characteristic f i := rfl

@[simp] theorem chart_source (i : Fin k) : (chart f i).source = ball 0 1 := rfl

@[simp] theorem chart_target (i : Fin k) : (chart f i).target =
    characteristic f i '' ball 0 1 := rfl

theorem chart_continuousOn (i : Fin k) :
    ContinuousOn (chart f i) (closedBall 0 1) := characteristic_continuousOn f i

theorem chart_continuousOn_symm (i : Fin k) :
    ContinuousOn (chart f i).symm (chart f i).target := by
  rw [← (chart f i).image_source_eq_target]
  exact (characteristic_isOpenEmbedding f i).isOpenMap.continuousOn_image_of_leftInvOn
    (chart f i).leftInvOn

variable [T2Space X] [CompactSpace X] [Nonempty X]
variable [CWComplex (univ : Set X)]

def oldChart (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    PartialEquiv (Fin n → ℝ) (Space f) :=
  (RelCWComplex.map n i).trans
    ((Adjunction.old_isClosedEmbedding (boundary_closed k d) f).isEmbedding.toPartialHomeomorph
      (Adjunction.old f)).toPartialEquiv

@[simp] theorem oldChart_apply (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n)
    (v : Fin n → ℝ) : oldChart f n i v = Adjunction.old f (RelCWComplex.map n i v) := rfl

@[simp] theorem oldChart_source (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    (oldChart f n i).source = ball 0 1 := by
  simp [oldChart, PartialEquiv.trans_source, RelCWComplex.source_eq]

theorem oldChart_continuousOn (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    ContinuousOn (oldChart f n i) (closedBall 0 1) :=
  (Adjunction.continuous_old f).comp_continuousOn (RelCWComplex.continuousOn n i)

theorem oldChart_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    ContinuousOn (oldChart f n i).symm (oldChart f n i).target := by
  let e := (Adjunction.old_isClosedEmbedding (boundary_closed k d) f).isEmbedding.toPartialHomeomorph
    (Adjunction.old f)
  change ContinuousOn ((RelCWComplex.map n i).symm ∘ e.symm)
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono inter_subset_left) (fun _ h => h.2)

def NewCell (n : ℕ) := RelCWComplex.cell (univ : Set X) n ⊕ (Fin k × PLift (n = d))

def newChart (n : ℕ) : NewCell (X := X) (k := k) (d := d) n →
    PartialEquiv (Fin n → ℝ) (Space f)
  | Sum.inl i => oldChart f n i
  | Sum.inr ⟨i, ⟨h⟩⟩ => h.symm ▸ chart f i

@[simp] theorem newChart_old (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) :
    newChart f n (Sum.inl i) = oldChart f n i := rfl

@[simp] theorem newChart_new (i : Fin k) :
    newChart f d (Sum.inr ⟨i, ⟨rfl⟩⟩) = chart f i := rfl

theorem newChart_source (n : ℕ) (i : NewCell (X := X) (k := k) (d := d) n) :
    (newChart f n i).source = ball 0 1 := by
  rcases i with i | ⟨i, ⟨h⟩⟩
  · exact oldChart_source f n i
  · subst n
    exact chart_source f i

theorem newChart_continuousOn (n : ℕ)
    (i : NewCell (X := X) (k := k) (d := d) n) :
    ContinuousOn (newChart f n i) (closedBall 0 1) := by
  rcases i with i | ⟨i, ⟨h⟩⟩
  · exact oldChart_continuousOn f n i
  · subst n
    exact chart_continuousOn f i

theorem newChart_continuousOn_symm (n : ℕ)
    (i : NewCell (X := X) (k := k) (d := d) n) :
    ContinuousOn (newChart f n i).symm (newChart f n i).target := by
  rcases i with i | ⟨i, ⟨h⟩⟩
  · exact oldChart_continuousOn_symm f n i
  · subst n
    exact chart_continuousOn_symm f i

omit [T2Space X] [CompactSpace X] [Nonempty X] [CWComplex (univ : Set X)] in
@[simp] theorem chart_apply_ball (i : Fin k) (v : Fin d → ℝ) (hv : v ∈ ball 0 1) :
    chart f i v = Adjunction.disk f (i, interiorInDisk ⟨v, hv⟩) :=
  characteristic_on_disk f i (interiorInDisk ⟨v, hv⟩)

omit [T2Space X] [CompactSpace X] [Nonempty X] [CWComplex (univ : Set X)] in
theorem chart_apply_sphere (i : Fin k) (v : Fin d → ℝ) (hv : v ∈ sphere 0 1) :
    chart f i v = Adjunction.old f
      (f ⟨(i, ⟨v, sphere_subset_closedBall hv⟩), hv⟩) := by
  rw [chart_coe, characteristic_on_disk f i ⟨v, sphere_subset_closedBall hv⟩]
  exact Adjunction.disk_boundary f ⟨(i, ⟨v, sphere_subset_closedBall hv⟩), hv⟩

theorem newChart_cell_eq {n m : ℕ}
    (i : NewCell (X := X) (k := k) (d := d) n)
    (j : NewCell (X := X) (k := k) (d := d) m)
    {v : Fin n → ℝ} {w : Fin m → ℝ} (hv : v ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (he : newChart f n i v = newChart f m j w) :
    (⟨n, i⟩ : Σ n, NewCell (X := X) (k := k) (d := d) n) = ⟨m, j⟩ := by
  classical
  rcases i with i | ⟨i, ⟨hi⟩⟩ <;> rcases j with j | ⟨j, ⟨hj⟩⟩
  · have hx : RelCWComplex.map n i v = RelCWComplex.map m j w :=
      (Adjunction.old_inj f).mp he
    by_cases hij : (⟨n, i⟩ : Σ n, RelCWComplex.cell (univ : Set X) n) = ⟨m, j⟩
    · cases hij
      rfl
    · exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hij)
        ⟨v, hv, rfl⟩ ⟨w, hw, hx.symm⟩)
  · subst m
    have he' : Adjunction.old f (RelCWComplex.map n i v) =
        Adjunction.disk f (j, interiorInDisk ⟨w, hw⟩) := by
      simpa only [newChart_old, oldChart_apply, newChart_new, chart_apply_ball f j w hw] using he
    exact False.elim (Adjunction.old_ne_disk_of_notMem f _
      (interiorInFamily j ⟨w, hw⟩).property he')
  · subst n
    have he' : Adjunction.old f (RelCWComplex.map m j w) =
        Adjunction.disk f (i, interiorInDisk ⟨v, hv⟩) := by
      simpa only [newChart_old, oldChart_apply, newChart_new, chart_apply_ball f i v hv] using he.symm
    exact False.elim (Adjunction.old_ne_disk_of_notMem f _
      (interiorInFamily i ⟨v, hv⟩).property he')
  · subst n
    subst m
    have he' : Adjunction.disk f (i, interiorInDisk ⟨v, hv⟩) =
        Adjunction.disk f (j, interiorInDisk ⟨w, hw⟩) := by
      simpa only [newChart_new, chart_apply_ball f i v hv, chart_apply_ball f j w hw] using he
    have he'' := (Adjunction.disk_eq_disk_of_notMem f
      (interiorInFamily i ⟨v, hv⟩).property).mp he'
    have hij : i = j := congrArg Prod.fst he''
    subst j
    rfl

theorem newChart_pairwiseDisjoint :
    (univ : Set (Σ n, NewCell (X := X) (k := k) (d := d) n)).PairwiseDisjoint
      (fun ni => newChart f ni.1 ni.2 '' ball 0 1) := by
  rintro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
  apply Set.disjoint_left.mpr
  rintro x ⟨v, hv, rfl⟩ ⟨w, hw, he⟩
  exact hne (newChart_cell_eq f i j hv hw he.symm)

variable (hdim : ∀ n, RelCWComplex.cell (univ : Set X) n → n < d)

include hdim in
theorem newChart_mapsTo (n : ℕ) (i : NewCell (X := X) (k := k) (d := d) n) :
    MapsTo (newChart f n i) (sphere 0 1)
      (⋃ (m < n) (j : NewCell (X := X) (k := k) (d := d) m),
        newChart f m j '' closedBall 0 1) := by
  rcases i with i | ⟨i, ⟨hi⟩⟩
  · obtain ⟨I, hI⟩ := CWComplex.mapsTo n i
    intro v hv
    have hh := hI hv
    simp only [mem_iUnion, mem_image] at hh ⊢
    obtain ⟨m, hm, j, _, w, hw, he⟩ := hh
    refine ⟨m, hm, Sum.inl j, w, hw, ?_⟩
    exact congrArg (Adjunction.old f) he
  · subst n
    intro v hv
    let y : boundary k d := ⟨(i, ⟨v, sphere_subset_closedBall hv⟩), hv⟩
    have hy : f y ∈ ⋃ (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m),
        RelCWComplex.closedCell m j := by
      rw [CWComplex.union]
      trivial
    simp only [mem_iUnion, RelCWComplex.closedCell, mem_image] at hy
    obtain ⟨m, j, w, hw, he⟩ := hy
    simp only [mem_iUnion, mem_image]
    refine ⟨m, hdim m j, Sum.inl j, w, hw, ?_⟩
    change Adjunction.old f (RelCWComplex.map m j w) = chart f i v
    rw [he, chart_apply_sphere f i v hv]

theorem newChart_union :
    (⋃ (n : ℕ) (i : NewCell (X := X) (k := k) (d := d) n),
      newChart f n i '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨x | ⟨i, v⟩, rfl⟩ := Quotient.mk_surjective z
  · have hx : x ∈ ⋃ (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m),
        RelCWComplex.closedCell m j := by
      rw [CWComplex.union]
      trivial
    simp only [mem_iUnion, RelCWComplex.closedCell, mem_image] at hx
    obtain ⟨n, i, v, hv, he⟩ := hx
    simp only [mem_iUnion, mem_image]
    exact ⟨n, Sum.inl i, v, hv, congrArg (Adjunction.old f) he⟩
  · simp only [mem_iUnion, mem_image]
    exact ⟨d, Sum.inr ⟨i, ⟨rfl⟩⟩, v.1, v.2, characteristic_on_disk f i v⟩

include hdim in
omit [T2Space X] [CompactSpace X] [Nonempty X] in
theorem newCell_eventually_isEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (NewCell (X := X) (k := k) (d := d) n) := by
  refine Filter.eventually_atTop.mpr ⟨d + 1, ?_⟩
  intro n hn
  refine ⟨?_⟩
  rintro (i | ⟨i, ⟨hi⟩⟩)
  · have := hdim n i
    omega
  · omega

variable [RelCWComplex.FiniteType (univ : Set X)]

omit [T2Space X] [CompactSpace X] [Nonempty X] in
theorem newCell_finite (n : ℕ) :
    Finite (NewCell (X := X) (k := k) (d := d) n) := by
  let : Finite (RelCWComplex.cell (univ : Set X) n) :=
    RelCWComplex.FiniteType.finite_cell n
  unfold NewCell
  infer_instance

@[instance_reducible] def cwComplex : CWComplex (univ : Set (Space f)) :=
  CWComplex.mkFinite univ (NewCell (X := X) (k := k) (d := d)) (newChart f)
    (newCell_eventually_isEmpty hdim) newCell_finite (newChart_source f)
    (newChart_continuousOn f) (newChart_continuousOn_symm f)
    (newChart_pairwiseDisjoint f) (newChart_mapsTo f hdim) (newChart_union f)

theorem cwComplex_finite :
    letI := cwComplex f hdim
    RelCWComplex.Finite (univ : Set (Space f)) := by
  let := cwComplex f hdim
  exact { eventually_isEmpty_cell := newCell_eventually_isEmpty hdim
          finite_cell := newCell_finite }

end

instance disk_pathConnectedSpace (d : ℕ) : PathConnectedSpace (Disk d) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : Fin d → ℝ) (1 : ℝ)).isPathConnected
      ⟨0, by simp⟩)

def boundaryVector (d : ℕ) : Fin d → ℝ := fun _ => -1

theorem boundaryVector_mem_sphere {d : ℕ} (hd : 0 < d) :
    boundaryVector d ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  change ‖(fun _ : Fin d => (-1 : ℝ)) - 0‖ = 1
  simp

theorem pathConnectedSpace {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    {k d : ℕ} (f : C(boundary k d, X)) (hd : 0 < d) : PathConnectedSpace (Space f) := by
  classical
  let x : X := Classical.choice PathConnectedSpace.nonempty
  have hx : ∀ z : Space f, Joined (Adjunction.old f x) z := by
    intro z
    obtain ⟨xz | ⟨i, v⟩, rfl⟩ := Quotient.mk_surjective z
    · exact (PathConnectedSpace.joined x xz).map (Adjunction.continuous_old f)
    · let u : Disk d := ⟨boundaryVector d,
        Metric.sphere_subset_closedBall (boundaryVector_mem_sphere hd)⟩
      let b : boundary k d := ⟨(i, u), boundaryVector_mem_sphere hd⟩
      have h₁ := (PathConnectedSpace.joined x (f b)).map (Adjunction.continuous_old f)
      have h₂ := (PathConnectedSpace.joined u v).map
        (f := fun z => Adjunction.disk f (i, z))
        ((Adjunction.continuous_disk f).comp (continuous_const.prodMk continuous_id))
      rw [Adjunction.disk_boundary f b] at h₂
      exact h₁.trans h₂
  exact ⟨⟨Adjunction.old f x⟩, fun a b => (hx a).symm.trans (hx b)⟩

end Cells

namespace Rose

abbrev Point := PUnit

instance point_finiteType : RelCWComplex.FiniteType (univ : Set Point) where
  finite_cell n := by
    cases n with
    | zero => change Finite (univ : Set Point); infer_instance
    | succ n => change Finite PEmpty; infer_instance

theorem point_dimension (n : ℕ) (i : RelCWComplex.cell (univ : Set Point) n) : n < 1 := by
  cases n with
  | zero => omega
  | succ n => exact PEmpty.elim i

def attaching (k : ℕ) : C(Cells.boundary k 1, Point) := ContinuousMap.const _ PUnit.unit

abbrev Space (k : ℕ) := Cells.Space (attaching k)

instance (k : ℕ) : CWComplex (univ : Set (Space k)) :=
  Cells.cwComplex (attaching k) point_dimension

instance (k : ℕ) : RelCWComplex.Finite (univ : Set (Space k)) :=
  Cells.cwComplex_finite (attaching k) point_dimension

instance (k : ℕ) : PathConnectedSpace (Space k) :=
  Cells.pathConnectedSpace (attaching k) (by decide)

theorem dimension (k n : ℕ) (i : RelCWComplex.cell (univ : Set (Space k)) n) : n < 2 := by
  change Cells.NewCell (X := Point) (k := k) (d := 1) n at i
  rcases i with i | ⟨i, ⟨h⟩⟩
  · have := point_dimension n i
    omega
  · omega

def basepoint (k : ℕ) : Space k := Adjunction.old (attaching k) PUnit.unit

instance (k : ℕ) : Nonempty (Space k) := ⟨basepoint k⟩

private def leftEnd : Fin 1 → ℝ := fun _ => -1
private def rightEnd : Fin 1 → ℝ := fun _ => 1

private theorem leftEnd_sphere : leftEnd ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  change ‖(fun _ : Fin 1 => (-1 : ℝ)) - 0‖ = 1
  simp

private theorem rightEnd_sphere : rightEnd ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  change ‖(fun _ : Fin 1 => (1 : ℝ)) - 0‖ = 1
  simp

private theorem segmentInDisk :
    Set.range (Path.segment leftEnd rightEnd) ⊆ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
  rw [Path.range_segment]
  exact (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset
    (Metric.sphere_subset_closedBall leftEnd_sphere)
    (Metric.sphere_subset_closedBall rightEnd_sphere)

def generatorLoop {k : ℕ} (i : Fin k) : Path (basepoint k) (basepoint k) :=
  ((Path.segment leftEnd rightEnd).map'
    ((Cells.characteristic_continuousOn (attaching k) i).mono segmentInDisk)).cast
    (by
      change basepoint k = Cells.chart (attaching k) i leftEnd
      rw [Cells.chart_apply_sphere (attaching k) i leftEnd leftEnd_sphere]
      rfl)
    (by
      change basepoint k = Cells.chart (attaching k) i rightEnd
      rw [Cells.chart_apply_sphere (attaching k) i rightEnd rightEnd_sphere]
      rfl)

def letterLoop {k : ℕ} (a : Fin k × Bool) : Path (basepoint k) (basepoint k) :=
  if a.2 then generatorLoop a.1 else (generatorLoop a.1).symm

def wordLoop {k : ℕ} : List (Fin k × Bool) → Path (basepoint k) (basepoint k)
  | [] => Path.refl _
  | a :: w => (wordLoop w).trans (letterLoop a)

def freeToFundamental (k : ℕ) : FreeGroup (Fin k) →* FundamentalGroup (Space k) (basepoint k) :=
  FreeGroup.lift (fun i => ⟦generatorLoop i⟧)

theorem freeToFundamental_mk {k : ℕ} (w : List (Fin k × Bool)) :
    freeToFundamental k (FreeGroup.mk w) = ⟦wordLoop w⟧ := by
  let : Group (Quotient (Path.Homotopic.setoid (basepoint k) (basepoint k))) :=
    inferInstanceAs (Group (FundamentalGroup (Space k) (basepoint k)))
  change (w.map (fun a => cond a.2
    (⟦generatorLoop a.1⟧ : FundamentalGroup (Space k) (basepoint k))
    (⟦generatorLoop a.1⟧ : FundamentalGroup (Space k) (basepoint k))⁻¹)).prod = _
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b <;> simp only [List.map_cons, List.prod_cons, ih, Bool.cond_false,
      Bool.cond_true, wordLoop, letterLoop, Bool.false_eq_true, ↓reduceIte]
    <;> rfl

end Rose

namespace AttachingLoops

open scoped unitInterval

def onCircle {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) :
    C(AddCircle (1 : ℝ), X) where
  toFun := AddCircle.liftIco 1 0 γ.extend
  continuous_toFun := AddCircle.liftIco_zero_continuous
    (by rw [γ.extend_zero, γ.extend_one]) γ.continuous_extend.continuousOn

abbrev SquareBoundary := (Metric.sphere (0 : Fin 2 → ℝ) 1 : Set (Fin 2 → ℝ))

def vectorComplex (v : Fin 2 → ℝ) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

@[simp] theorem vectorComplex_re (v : Fin 2 → ℝ) : (vectorComplex v).re = v 0 := by
  simp [vectorComplex]

@[simp] theorem vectorComplex_im (v : Fin 2 → ℝ) : (vectorComplex v).im = v 1 := by
  simp [vectorComplex]

theorem vectorComplex_continuous : Continuous vectorComplex := by
  unfold vectorComplex
  fun_prop

theorem vectorComplex_ne_zero (v : SquareBoundary) : vectorComplex v.1 ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [vectorComplex_re, vectorComplex_im, Complex.zero_re, Complex.zero_im] at hr hi
  have hv : v.1 = 0 := by
    funext i
    fin_cases i <;> assumption
  have hh := v.property
  rw [hv] at hh
  norm_num at hh

def boundaryAngle : C(SquareBoundary, Real.Angle) where
  toFun v := (Complex.arg (vectorComplex v.1) : Real.Angle)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (Complex.continuousAt_arg_coe_angle (vectorComplex_ne_zero v)).comp
      (f := fun z : SquareBoundary => vectorComplex z.1)
      (vectorComplex_continuous.comp continuous_subtype_val).continuousAt

def boundaryParameter : C(SquareBoundary, AddCircle (1 : ℝ)) :=
  let e := AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  (⟨e, e.continuous⟩ : C(Real.Angle, AddCircle (1 : ℝ))).comp boundaryAngle

def complexVector (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

@[simp] theorem vectorComplex_complexVector (z : ℂ) :
    vectorComplex (complexVector z) = z := by
  simp [complexVector, vectorComplex, Complex.re_add_im]

theorem complexVector_continuous : Continuous complexVector := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

theorem complexVector_ne_zero (z : Circle) : complexVector z ≠ 0 := by
  intro h
  have hh := congrArg vectorComplex h
  simp only [vectorComplex_complexVector] at hh
  have hzero : vectorComplex 0 = 0 := by simp [vectorComplex]
  exact z.coe_ne_zero (hh.trans hzero)

def squareOfCircle : C(Circle, SquareBoundary) where
  toFun z := ((homeomorphUnitSphereProd (Fin 2 → ℝ))
    ⟨complexVector z, by simpa using complexVector_ne_zero z⟩).1
  continuous_toFun := continuous_fst.comp
    ((homeomorphUnitSphereProd (Fin 2 → ℝ)).continuous.comp
      ((complexVector_continuous.comp continuous_subtype_val).subtype_mk
        (fun z => by simpa using complexVector_ne_zero z)))

theorem boundaryAngle_squareOfCircle (z : Circle) :
    boundaryAngle (squareOfCircle z) = (Complex.arg z : Real.Angle) := by
  simp only [boundaryAngle, ContinuousMap.coe_mk, squareOfCircle,
    homeomorphUnitSphereProd_apply_fst_coe]
  change (Complex.arg (vectorComplex (‖complexVector z‖⁻¹ • complexVector z)) :
    Real.Angle) = _
  have hlin : ∀ (a : ℝ) (v : Fin 2 → ℝ),
      vectorComplex (a • v) = (a : ℂ) * vectorComplex v := by
    intro a v
    simp [vectorComplex, mul_add, mul_assoc]
  rw [hlin, vectorComplex_complexVector, Complex.arg_real_mul]
  exact inv_pos.mpr (norm_pos_iff.mpr (complexVector_ne_zero z))

def boundaryLift : C(AddCircle (1 : ℝ), SquareBoundary) :=
  let e := AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  squareOfCircle.comp ((⟨AddCircle.homeomorphCircle',
    AddCircle.homeomorphCircle'.continuous⟩ : C(Real.Angle, Circle)).comp
      ⟨e.symm, e.symm.continuous⟩)

@[simp] theorem boundaryParameter_boundaryLift (z : AddCircle (1 : ℝ)) :
    boundaryParameter (boundaryLift z) = z := by
  change AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _
    (boundaryAngle (squareOfCircle (AddCircle.homeomorphCircle'
      ((AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _).symm z)))) = z
  rw [boundaryAngle_squareOfCircle]
  change AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _
    (AddCircle.homeomorphCircle'.symm (AddCircle.homeomorphCircle' _)) = z
  simp only [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]

def boundaryLoop : Path (boundaryLift 0) (boundaryLift 0) where
  toFun t := boundaryLift ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := boundaryLift.continuous.comp
    (continuous_quotient_mk'.comp continuous_subtype_val)
  source' := by simp
  target' := by
    change boundaryLift ((1 : ℝ) : AddCircle (1 : ℝ)) = boundaryLift 0
    rw [AddCircle.coe_period]

@[simp] theorem onCircle_coe {X : Type*} [TopologicalSpace X] {x : X}
    (γ : Path x x) (t : unitInterval) :
    onCircle γ ((t : ℝ) : AddCircle (1 : ℝ)) = γ t := by
  by_cases h : (t : ℝ) = 1
  · have ht : t = 1 := Subtype.ext h
    subst t
    change AddCircle.liftIco 1 0 γ.extend ((1 : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_period]
    rw [← AddCircle.coe_zero, AddCircle.liftIco_zero_coe_apply (by norm_num)]
    simp
  · change AddCircle.liftIco 1 0 γ.extend ((t : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, lt_of_le_of_ne t.property.2 h⟩]
    exact γ.extend_apply t.property

def relators {k r : ℕ} (w : Fin r → List (Fin k × Bool)) :
    C(Cells.boundary r 2, Rose.Space k) where
  toFun b := onCircle (Rose.wordLoop (w b.1.1)) (boundaryParameter ⟨b.1.2.1, b.2⟩)
  continuous_toFun := by
    have hf : Continuous (fun p : Fin r × AddCircle (1 : ℝ) =>
        onCircle (Rose.wordLoop (w p.1)) p.2) :=
      continuous_prod_of_discrete_left.mpr fun i => (onCircle (Rose.wordLoop (w i))).continuous
    have hp : Continuous (fun b : Cells.boundary r 2 =>
        boundaryParameter ⟨b.1.2.1, b.2⟩) :=
      boundaryParameter.continuous.comp
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).prodMk hp)

end AttachingLoops

namespace PresentationComplex

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

abbrev Space := Cells.Space (AttachingLoops.relators w)

instance : CWComplex (univ : Set (Space w)) :=
  Cells.cwComplex (AttachingLoops.relators w) (Rose.dimension k)

instance : RelCWComplex.Finite (univ : Set (Space w)) :=
  Cells.cwComplex_finite (AttachingLoops.relators w) (Rose.dimension k)

instance : PathConnectedSpace (Space w) :=
  Cells.pathConnectedSpace (AttachingLoops.relators w) (by decide)

theorem dimension (n : ℕ) (i : RelCWComplex.cell (univ : Set (Space w)) n) : n < 3 := by
  change Cells.NewCell (X := Rose.Space k) (k := r) (d := 2) n at i
  rcases i with i | ⟨i, ⟨h⟩⟩
  · have := Rose.dimension k n i
    omega
  · omega

def basepoint : Space w := Adjunction.old (AttachingLoops.relators w) (Rose.basepoint k)

def includeRose : C(Rose.Space k, Space w) :=
  ⟨Adjunction.old (AttachingLoops.relators w), Adjunction.continuous_old _⟩

def freeToFundamental : FreeGroup (Fin k) →* FundamentalGroup (Space w) (basepoint w) :=
  (FundamentalGroup.map (includeRose w) (Rose.basepoint k)).comp (Rose.freeToFundamental k)

def diskMap (i : Fin r) : C(Cells.Disk 2, Space w) :=
  ⟨fun v => Adjunction.disk (AttachingLoops.relators w) (i, v),
    (Adjunction.continuous_disk _).comp (continuous_const.prodMk continuous_id)⟩

def boundaryInDisk : C(AttachingLoops.SquareBoundary, Cells.Disk 2) :=
  ⟨fun b => ⟨b.1, Metric.sphere_subset_closedBall b.2⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem diskMap_boundary (i : Fin r) (b : AttachingLoops.SquareBoundary) :
    diskMap w i (boundaryInDisk b) = includeRose w
      (AttachingLoops.onCircle (Rose.wordLoop (w i)) (AttachingLoops.boundaryParameter b)) :=
  Adjunction.disk_boundary (AttachingLoops.relators w)
    ⟨(i, boundaryInDisk b), b.2⟩

theorem diskMap_boundary_basepoint (i : Fin r) :
    diskMap w i (boundaryInDisk (AttachingLoops.boundaryLift 0)) = basepoint w := by
  rw [diskMap_boundary, AttachingLoops.boundaryParameter_boundaryLift]
  have hh := AttachingLoops.onCircle_coe (Rose.wordLoop (w i)) 0
  change includeRose w _ = includeRose w (Rose.basepoint k)
  simpa using congrArg (includeRose w) hh

def filledRelatorLoop (i : Fin r) : Path (basepoint w) (basepoint w) :=
  (((AttachingLoops.boundaryLoop).map boundaryInDisk.continuous).map
    (diskMap w i).continuous).cast
      (diskMap_boundary_basepoint w i).symm (diskMap_boundary_basepoint w i).symm

theorem filledRelatorLoop_eq (i : Fin r) :
    filledRelatorLoop w i = (Rose.wordLoop (w i)).map (includeRose w).continuous := by
  ext t
  change diskMap w i (boundaryInDisk (AttachingLoops.boundaryLift
    ((t : ℝ) : AddCircle (1 : ℝ)))) = includeRose w (Rose.wordLoop (w i) t)
  rw [diskMap_boundary, AttachingLoops.boundaryParameter_boundaryLift,
    AttachingLoops.onCircle_coe]

theorem relator_nullhomotopic (i : Fin r) :
    ((Rose.wordLoop (w i)).map (includeRose w).continuous).Homotopic
      (Path.refl (basepoint w)) := by
  let : ContractibleSpace (Cells.Disk 2) := Metric.contractibleSpace_closedBall (by norm_num)
  have h := SimplyConnectedSpace.paths_homotopic
    (AttachingLoops.boundaryLoop.map boundaryInDisk.continuous)
    (Path.refl (boundaryInDisk (AttachingLoops.boundaryLift 0)))
  have hh := (h.map (diskMap w i)).pathCast
    (diskMap_boundary_basepoint w i).symm (diskMap_boundary_basepoint w i).symm
  change (filledRelatorLoop w i).Homotopic _ at hh
  rw [filledRelatorLoop_eq] at hh
  have href : ((Path.refl (boundaryInDisk (AttachingLoops.boundaryLift 0))).map
      (diskMap w i).continuous).cast
      (diskMap_boundary_basepoint w i).symm (diskMap_boundary_basepoint w i).symm =
      Path.refl (basepoint w) := by
    ext t
    exact diskMap_boundary_basepoint w i
  rw [href] at hh
  exact hh

theorem freeToFundamental_relator (i : Fin r) :
    freeToFundamental w (FreeGroup.mk (w i)) = 1 := by
  change FundamentalGroup.map (includeRose w) (Rose.basepoint k)
    (Rose.freeToFundamental k (FreeGroup.mk (w i))) = _
  rw [Rose.freeToFundamental_mk]
  exact Quotient.sound (relator_nullhomotopic w i)

def relatorSet : Set (FreeGroup (Fin k)) := Set.range (fun i => FreeGroup.mk (w i))

def presentedToFundamental : PresentedGroup (relatorSet w) →*
    FundamentalGroup (Space w) (basepoint w) :=
  QuotientGroup.lift (Subgroup.normalClosure (relatorSet w)) (freeToFundamental w)
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨i, rfl⟩
      exact freeToFundamental_relator w i))

@[simp]
theorem presentedToFundamental_mk (g : FreeGroup (Fin k)) :
    presentedToFundamental w (PresentedGroup.mk (relatorSet w) g) =
      freeToFundamental w g := rfl

def PresentationTheoremObligation.{u} : Prop :=
  Function.Bijective (presentedToFundamental.{u} w)

end PresentationComplex

end PresentationGeometry

end

end OAI
