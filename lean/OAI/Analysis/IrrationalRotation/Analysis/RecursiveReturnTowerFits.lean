import OAI.Analysis.IrrationalRotation.Analysis.RecursiveReturnTowers
import OAI.Analysis.IrrationalRotation.Analysis.TowerItineraryFits

namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace Invariant233.FiniteReturnTower

variable {X : Type*} [MeasurableSpace X] {f : X ≃ᵐ X}

def baseLabel (P : FiniteReturnTower f) (i : P.Index) : P.LevelIndex :=
  ⟨i, ⟨0, P.height_pos i⟩⟩

@[simp] theorem level_baseLabel (P : FiniteReturnTower f) (i : P.Index) :
    P.level (P.baseLabel i) = P.base i := by
  simp [baseLabel, level, TowerItinerary.indexedLevel, TowerItinerary.level]

@[simp] theorem color_fiber_baseLabel (P : FiniteReturnTower f) (i : P.Index) :
    P.color ⁻¹' {P.baseLabel i} = P.base i := by
  rw [P.color_fiber, P.level_baseLabel]

def fittingBaseLevels (P Q : FiniteReturnTower f) (i : P.Index) :
    Finset (P.refine Q).LevelIndex :=
  TowerItineraryFits.fittingColorLevels Q.height (P.baseLabel i) (P.height i)

theorem fittingBaseLevels_fits (P Q : FiniteReturnTower f) (i : P.Index)
    (a : (P.refine Q).LevelIndex) (ha : a ∈ P.fittingBaseLevels Q i) :
    a.2.val + P.height i ≤ (P.refine Q).height a.1 :=
  (TowerItineraryFits.mem_fittingColorLevels Q.height (P.baseLabel i)
    (P.height i) a).mp ha |>.2

theorem base_eq_refine_fitting_union (P Q : FiniteReturnTower f)
    (hnest : Q.returnBase ⊆ P.returnBase) (i : P.Index) :
    P.base i = ⋃ a ∈ P.fittingBaseLevels Q i, (P.refine Q).level a := by
  rw [← P.color_fiber_baseLabel i]
  apply TowerItineraryFits.colorFiber_eq_fitting_finset_union f P.color
    Q.base Q.height P.returnBase (P.baseLabel i) (P.height i) Q.covers
  · intro j z hz
    exact hnest (Q.top_mem j z hz)
  · intro y hy
    have hymem : y ∈ P.base i := by
      have : y ∈ P.color ⁻¹' {P.baseLabel i} := hy
      rwa [P.color_fiber_baseLabel] at this
    exact P.no_return i y hymem

theorem indicator_base_eq_refine_fitting_sum (P Q : FiniteReturnTower f)
    (hnest : Q.returnBase ⊆ P.returnBase) (i : P.Index)
    {E : Type*} [AddCommMonoid E] (g : X → E) (x : X) :
    (P.base i).indicator g x = ∑ a ∈ P.fittingBaseLevels Q i,
      ((P.refine Q).level a).indicator g x := by
  classical
  rw [base_eq_refine_fitting_union P Q hnest i]
  apply Finset.indicator_biUnion_apply
  intro a ha b hb hab
  exact (P.refine Q).disjoint hab

def successorBaseLevels (raw : ℕ → FiniteReturnTower f) (n : ℕ)
    (i : (sequence raw n).Index) : Finset (sequence raw (n + 1)).LevelIndex :=
  (sequence raw n).fittingBaseLevels (raw (n + 1)) i

theorem sequence_base_eq_successor_fitting_union (raw : ℕ → FiniteReturnTower f)
    (hnest : ∀ n, (raw (n + 1)).returnBase ⊆ (raw n).returnBase)
    (n : ℕ) (i : (sequence raw n).Index) :
    (sequence raw n).base i =
      ⋃ a ∈ successorBaseLevels raw n i, (sequence raw (n + 1)).level a := by
  apply base_eq_refine_fitting_union (sequence raw n) (raw (n + 1))
  simpa only [sequence_returnBase] using hnest n

theorem sequence_successorBaseLevels_fits (raw : ℕ → FiniteReturnTower f)
    (n : ℕ) (i : (sequence raw n).Index)
    (a : (sequence raw (n + 1)).LevelIndex) (ha : a ∈ successorBaseLevels raw n i) :
    a.2.val + (sequence raw n).height i ≤ (sequence raw (n + 1)).height a.1 :=
  fittingBaseLevels_fits (sequence raw n) (raw (n + 1)) i a ha

theorem sequence_indicator_base_eq_successor_sum (raw : ℕ → FiniteReturnTower f)
    (hnest : ∀ n, (raw (n + 1)).returnBase ⊆ (raw n).returnBase)
    (n : ℕ) (i : (sequence raw n).Index)
    {E : Type*} [AddCommMonoid E] (g : X → E) (x : X) :
    ((sequence raw n).base i).indicator g x =
      ∑ a ∈ successorBaseLevels raw n i, ((sequence raw (n + 1)).level a).indicator g x := by
  apply indicator_base_eq_refine_fitting_sum (sequence raw n) (raw (n + 1))
  simpa only [sequence_returnBase] using hnest n

end Invariant233.FiniteReturnTower

end

end OAI
