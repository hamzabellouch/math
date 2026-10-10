import OAI.Analysis.IrrationalRotation.Analysis.TowerItineraryRefinement
import OAI.Analysis.IrrationalRotation.Analysis.NestedReturnSegments

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.TowerItineraryFits
open TowerItinerary

variable {X ι κ : Type*}

theorem offset_fits_of_nonempty (f : X → X) (c : X → κ)
    (B : ι → Set X) (height : ι → ℕ) (A : Set X) (t : κ) (oldHeight : ℕ)
    (hend : ∀ i z, z ∈ B i → f^[height i] z ∈ A)
    (havoid : ∀ y, c y = t → ∀ u : ℕ, 0 < u → u < oldHeight → f^[u] y ∉ A)
    (a : LevelIndex (refinedHeight height (κ := κ)))
    (hcol : a.1.2 a.2 = t)
    (hne : (bases f c B height a.1).Nonempty) :
    a.2.val + oldHeight ≤ height a.1.1 := by
  obtain ⟨z, hz⟩ := hne
  have hc : c (f^[a.2.val] z) = t := (congrFun hz.2 a.2).trans hcol
  exact NestedReturnSegments.return_segment_fits f a.2.isLt
    (hend a.1.1 z hz.1) (havoid _ hc)

section Finite
variable [Fintype ι] [Fintype κ]

def fittingColorLevels (height : ι → ℕ) (t : κ) (oldHeight : ℕ) :
    Finset (LevelIndex (refinedHeight height (κ := κ))) := by
  classical
  exact (colorLevels height t).filter fun a => a.2.val + oldHeight ≤ height a.1.1

@[simp] theorem mem_fittingColorLevels (height : ι → ℕ) (t : κ) (oldHeight : ℕ)
    (a : LevelIndex (refinedHeight height (κ := κ))) :
    a ∈ fittingColorLevels height t oldHeight ↔
      a.1.2 a.2 = t ∧ a.2.val + oldHeight ≤ height a.1.1 := by
  classical
  simp [fittingColorLevels]

theorem colorFiber_eq_fitting_finset_union (f : X → X) (c : X → κ)
    (B : ι → Set X) (height : ι → ℕ) (A : Set X) (t : κ) (oldHeight : ℕ)
    (hcover : ∀ x, ∃ i, ∃ k : Fin (height i), x ∈ level f B height i k)
    (hend : ∀ i z, z ∈ B i → f^[height i] z ∈ A)
    (havoid : ∀ y, c y = t → ∀ u : ℕ, 0 < u → u < oldHeight → f^[u] y ∉ A) :
    c ⁻¹' {t} = ⋃ a ∈ fittingColorLevels height t oldHeight,
      indexedLevel f (bases f c B height) (refinedHeight height) a := by
  rw [colorFiber_eq_finset_union f c B height hcover t]
  apply Set.ext
  intro x
  simp only [Set.mem_iUnion, mem_colorLevels, mem_fittingColorLevels]
  constructor
  · rintro ⟨a, ha, hx⟩
    have hne : (bases f c B height a.1).Nonempty := by
      obtain ⟨z, hz, _⟩ := hx
      exact ⟨z, hz⟩
    have hfit := offset_fits_of_nonempty f c B height A t oldHeight hend havoid a ha hne
    exact ⟨a, ⟨ha, hfit⟩, hx⟩
  · rintro ⟨a, ⟨ha, _⟩, hx⟩
    exact ⟨a, ha, hx⟩

theorem partitionAtom_eq_fitting_finset_union (f : X → X)
    (B : ι → Set X) (height : ι → ℕ) (A : Set X)
    (P : κ → Set X) (hPcover : ∀ x, ∃ t, x ∈ P t)
    (hPdisj : Pairwise (fun t u => Disjoint (P t) (P u))) (t : κ) (oldHeight : ℕ)
    (hcover : ∀ x, ∃ i, ∃ k : Fin (height i), x ∈ level f B height i k)
    (hend : ∀ i z, z ∈ B i → f^[height i] z ∈ A)
    (havoid : ∀ y ∈ P t, ∀ u : ℕ, 0 < u → u < oldHeight → f^[u] y ∉ A) :
    P t = ⋃ a ∈ fittingColorLevels height t oldHeight,
      indexedLevel f (bases f (partitionColor P hPcover) B height)
        (refinedHeight height) a := by
  rw [← partitionColor_fiber P hPcover hPdisj t]
  apply colorFiber_eq_fitting_finset_union f (partitionColor P hPcover)
    B height A t oldHeight hcover hend
  intro y hy
  apply havoid y
  have hy' : y ∈ partitionColor P hPcover ⁻¹' {t} := hy
  rwa [partitionColor_fiber P hPcover hPdisj t] at hy'

theorem indicator_colorFiber_eq_fitting_sum {f : X → X} (hf : Function.Injective f)
    (c : X → κ) (B : ι → Set X) (height : ι → ℕ) (A : Set X)
    (t : κ) (oldHeight : ℕ)
    (hcover : ∀ x, ∃ i, ∃ k : Fin (height i), x ∈ level f B height i k)
    (hdisj : Pairwise (fun a b : LevelIndex height =>
      Disjoint (indexedLevel f B height a) (indexedLevel f B height b)))
    (hend : ∀ i z, z ∈ B i → f^[height i] z ∈ A)
    (havoid : ∀ y, c y = t → ∀ u : ℕ, 0 < u → u < oldHeight → f^[u] y ∉ A)
    {E : Type*} [AddCommMonoid E] (g : X → E) (x : X) :
    (c ⁻¹' {t}).indicator g x =
      ∑ a ∈ fittingColorLevels height t oldHeight,
        (indexedLevel f (bases f c B height) (refinedHeight height) a).indicator g x := by
  classical
  rw [colorFiber_eq_fitting_finset_union f c B height A t oldHeight hcover hend havoid]
  apply Finset.indicator_biUnion_apply
  intro a ha b hb hab
  exact pairwiseDisjoint_refinedLevels hf c B height hdisj hab

end Finite
end Invariant233.TowerItineraryFits

end

end OAI
