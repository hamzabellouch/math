import OAI.Analysis.IrrationalRotation.Analysis.TowerItineraryRefinement

namespace OAI

noncomputable section
namespace Invariant233

open Set

variable {X : Type*} [MeasurableSpace X]

structure FiniteReturnTower (f : X ≃ᵐ X) where
  Index : Type
  indexFintype : Fintype Index
  height : Index → ℕ
  height_pos : ∀ i, 0 < height i
  base : Index → Set X
  returnBase : Set X
  base_measurable : ∀ i, MeasurableSet (base i)
  bases_cover : (⋃ i, base i) = returnBase
  top_mem : ∀ i x, x ∈ base i → (f : X → X)^[height i] x ∈ returnBase
  no_return : ∀ i x, x ∈ base i → ∀ k : ℕ, 0 < k → k < height i →
    (f : X → X)^[k] x ∉ returnBase
  disjoint : Pairwise fun a b : TowerItinerary.LevelIndex height =>
    Disjoint (TowerItinerary.indexedLevel f base height a)
      (TowerItinerary.indexedLevel f base height b)
  covers : ∀ x, ∃ i, ∃ k : Fin (height i),
    x ∈ TowerItinerary.level f base height i k

namespace FiniteReturnTower

attribute [instance] indexFintype

variable {f : X ≃ᵐ X}

abbrev LevelIndex (P : FiniteReturnTower f) := TowerItinerary.LevelIndex P.height

abbrev level (P : FiniteReturnTower f) (a : P.LevelIndex) : Set X :=
  TowerItinerary.indexedLevel f P.base P.height a

def color (P : FiniteReturnTower f) : X → P.LevelIndex :=
  TowerItinerary.partitionColor P.level (fun x => by
    obtain ⟨i, k, hx⟩ := P.covers x
    exact ⟨⟨i, k⟩, hx⟩)

theorem color_fiber (P : FiniteReturnTower f) (a : P.LevelIndex) :
    P.color ⁻¹' {a} = P.level a :=
  TowerItinerary.partitionColor_fiber _ _ P.disjoint a

theorem measurable_level (P : FiniteReturnTower f) (a : P.LevelIndex) :
    MeasurableSet (P.level a) :=
  TowerItinerary.measurableSet_iterate_image f (P.base_measurable a.1) a.2.val

theorem measurable_color (P : FiniteReturnTower f) [MeasurableSpace P.LevelIndex] :
    Measurable P.color :=
  TowerItinerary.measurable_partitionColor _ P.measurable_level _ P.disjoint

def refine (P Q : FiniteReturnTower f) : FiniteReturnTower f := by
  classical
  letI : MeasurableSpace P.LevelIndex := ⊤
  exact {
    Index := TowerItinerary.RefinedIndex Q.height P.LevelIndex
    indexFintype := inferInstance
    height := TowerItinerary.refinedHeight Q.height
    height_pos := fun a => Q.height_pos a.1
    base := TowerItinerary.bases f P.color Q.base Q.height
    returnBase := Q.returnBase
    base_measurable := fun a => TowerItinerary.measurableSet_refinedBase
      f.measurable P.measurable_color (Q.base_measurable a.1) (Q.height a.1) a.2
    bases_cover := by
      rw [← Q.bases_cover]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨⟨i, w⟩, hx⟩
        exact ⟨i, hx.1⟩
      · rintro ⟨i, hx⟩
        exact ⟨⟨i, TowerItinerary.word f P.color (Q.height i) x⟩, hx, rfl⟩
    top_mem := fun a x hx => Q.top_mem a.1 x hx.1
    no_return := fun a x hx => Q.no_return a.1 x hx.1
    disjoint := TowerItinerary.pairwiseDisjoint_refinedLevels f.injective
      P.color Q.base Q.height Q.disjoint
    covers := TowerItinerary.refined_covers f P.color Q.base Q.height Q.covers }

@[simp] theorem refine_returnBase (P Q : FiniteReturnTower f) :
    (P.refine Q).returnBase = Q.returnBase := rfl

@[simp] theorem refine_height (P Q : FiniteReturnTower f)
    (a : (P.refine Q).Index) : (P.refine Q).height a = Q.height a.1 := rfl

theorem refine_base_subset (P Q : FiniteReturnTower f) (a : (P.refine Q).Index) :
    (P.refine Q).base a ⊆ Q.base a.1 :=
  TowerItinerary.refinedBase_subset f P.color (Q.base a.1) (Q.height a.1) a.2

theorem level_eq_refine_union (P Q : FiniteReturnTower f) (a : P.LevelIndex) :
    P.level a = ⋃ b ∈ TowerItinerary.colorLevels Q.height a, (P.refine Q).level b := by
  rw [← P.color_fiber a]
  exact TowerItinerary.colorFiber_eq_finset_union f P.color Q.base Q.height Q.covers a

def sequence (raw : ℕ → FiniteReturnTower f) : ℕ → FiniteReturnTower f
  | 0 => raw 0
  | n + 1 => (sequence raw n).refine (raw (n + 1))

@[simp] theorem sequence_zero (raw : ℕ → FiniteReturnTower f) :
    sequence raw 0 = raw 0 := rfl

@[simp] theorem sequence_succ (raw : ℕ → FiniteReturnTower f) (n : ℕ) :
    sequence raw (n + 1) = (sequence raw n).refine (raw (n + 1)) := rfl

@[simp] theorem sequence_returnBase (raw : ℕ → FiniteReturnTower f) (n : ℕ) :
    (sequence raw n).returnBase = (raw n).returnBase := by
  cases n <;> rfl

theorem sequence_level_eq_successor_union (raw : ℕ → FiniteReturnTower f)
    (n : ℕ) (a : (sequence raw n).LevelIndex) :
    (sequence raw n).level a =
      ⋃ b ∈ TowerItinerary.colorLevels (raw (n + 1)).height a,
        (sequence raw (n + 1)).level b :=
  level_eq_refine_union (sequence raw n) (raw (n + 1)) a

def sequenceParent (raw : ℕ → FiniteReturnTower f) :
    (n : ℕ) → (sequence raw n).Index → (raw n).Index
  | 0, i => i
  | _ + 1, i => i.1

@[simp] theorem sequence_height_parent (raw : ℕ → FiniteReturnTower f)
    (n : ℕ) (i : (sequence raw n).Index) :
    (sequence raw n).height i = (raw n).height (sequenceParent raw n i) := by
  cases n <;> rfl

theorem sequence_base_subset_parent (raw : ℕ → FiniteReturnTower f)
    (n : ℕ) (i : (sequence raw n).Index) :
    (sequence raw n).base i ⊆ (raw n).base (sequenceParent raw n i) := by
  cases n with
  | zero => exact Subset.rfl
  | succ n => exact refine_base_subset (sequence raw n) (raw (n + 1)) i

def topUnion (P : FiniteReturnTower f) : Set X :=
  ⋃ i, (f : X → X)^[P.height i - 1] '' P.base i

@[simp] theorem refine_topUnion (P Q : FiniteReturnTower f) :
    (P.refine Q).topUnion = Q.topUnion := by
  ext x
  simp only [topUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, w⟩, y, hy, hxy⟩
    exact ⟨i, y, hy.1, hxy⟩
  · rintro ⟨i, y, hy, hxy⟩
    exact ⟨⟨i, TowerItinerary.word f P.color (Q.height i) y⟩,
      y, ⟨hy, rfl⟩, hxy⟩

@[simp] theorem sequence_topUnion (raw : ℕ → FiniteReturnTower f) (n : ℕ) :
    (sequence raw n).topUnion = (raw n).topUnion := by
  cases n with
  | zero => rfl
  | succ n => exact refine_topUnion (sequence raw n) (raw (n + 1))

def sequenceLevelParent (raw : ℕ → FiniteReturnTower f) (n : ℕ)
    (a : (sequence raw n).LevelIndex) : (raw n).LevelIndex :=
  ⟨sequenceParent raw n a.1, ⟨a.2.val, by
    rw [← sequence_height_parent raw n a.1]
    exact a.2.isLt⟩⟩

theorem sequence_level_subset_parent (raw : ℕ → FiniteReturnTower f)
    (n : ℕ) (a : (sequence raw n).LevelIndex) :
    (sequence raw n).level a ⊆ (raw n).level (sequenceLevelParent raw n a) :=
  Set.image_mono (sequence_base_subset_parent raw n a.1)

theorem measurable_returnBase (P : FiniteReturnTower f) :
    MeasurableSet P.returnBase := by
  rw [← P.bases_cover]
  exact MeasurableSet.iUnion P.base_measurable

theorem topUnion_eq_preimage (P : FiniteReturnTower f) :
    P.topUnion = f ⁻¹' P.returnBase := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    have hheight : P.height i - 1 + 1 = P.height i := by
      exact Nat.sub_add_cancel (P.height_pos i)
    change f ((f : X → X)^[P.height i - 1] y) ∈ P.returnBase
    rw [← Function.iterate_succ_apply' (f := (f : X → X)), Nat.succ_eq_add_one, hheight]
    exact P.top_mem i y hy
  · intro hx
    obtain ⟨i, k, y, hy, rfl⟩ := P.covers x
    have hnext : (f : X → X)^[k.val + 1] y ∈ P.returnBase := by
      simpa only [Function.iterate_succ_apply', Set.mem_preimage] using hx
    have hbound : P.height i ≤ k.val + 1 := by
      by_contra hbad
      exact P.no_return i y hy (k.val + 1) (Nat.succ_pos _) (by omega) hnext
    have htop : k.val = P.height i - 1 := by omega
    exact Set.mem_iUnion.mpr ⟨i, y, hy, by simp only [htop]⟩

theorem measure_topUnion (P : FiniteReturnTower f) (μ : MeasureTheory.Measure X)
    (hf : MeasureTheory.MeasurePreserving f μ μ) :
    μ P.topUnion = μ P.returnBase := by
  rw [P.topUnion_eq_preimage]
  exact hf.measure_preimage P.measurable_returnBase.nullMeasurableSet

end FiniteReturnTower
end Invariant233

end

end OAI
