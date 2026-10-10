import OAI.Analysis.CircleDomains.Selection.DustPriorContacts
import OAI.Analysis.CircleDomains.Selection.CountableDeletions

namespace OAI

/-! The countable data attached to a recursion stage: every earlier law is
retained, its hit support has finite deletions, and every required dust mark
is among the marks prescribed to the next positive-law construction. -/

open Set Function Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

structure PriorLawPresentation (B S : Set X) (μ : ℕ → Measure C(PathTime, X)) where
  marks : Set X
  marks_countable : marks.Countable
  marks_dust : marks ⊆ B
  extra_marks : S ⊆ marks
  prior_marks : ∀ i, support (dustPriorHitMass B (μ i)) ⊆ marks
  priorDeletions : ℕ → ℕ → Finset X
  prior_monotone : ∀ i, Monotone (priorDeletions i)
  prior_subset : ∀ i n, (priorDeletions i n : Set X) ⊆ support (priorHitMass (μ i))
  prior_cover : ∀ i x, x ∈ support (priorHitMass (μ i)) →
    ∀ᶠ n in atTop, x ∈ priorDeletions i n
  flagDeletions : ℕ → Finset X
  flag_monotone : Monotone flagDeletions
  flag_subset : ∀ n, (flagDeletions n : Set X) ⊆ S
  flag_cover : ∀ x ∈ S, ∀ᶠ n in atTop, x ∈ flagDeletions n

theorem nonempty_priorLawPresentation (B S : Set X) (μ : ℕ → Measure C(PathTime, X))
    (hS : S.Countable) (hSB : S ⊆ B)
    (hμ : ∀ i, (support (priorHitMass (μ i))).Countable) :
    Nonempty (PriorLawPresentation B S μ) := by
  classical
  let M := S ∪ ⋃ i, support (dustPriorHitMass B (μ i))
  have hM : M.Countable := hS.union (countable_iUnion fun i => by
    rw [support_dustPriorHitMass]
    exact (hμ i).mono inter_subset_right)
  have hMB : M ⊆ B := by
    rintro x (hx | hx)
    · exact hSB hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ((support_dustPriorHitMass B (μ i)) ▸ hi).1
  choose F hFm hFs hFc using fun i => exists_finite_deletions _ (hμ i)
  obtain ⟨L, hLm, hLs, hLc⟩ := exists_finite_deletions S hS
  exact ⟨{
    marks := M
    marks_countable := hM
    marks_dust := hMB
    extra_marks := subset_union_left
    prior_marks := fun i x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
    priorDeletions := F
    prior_monotone := hFm
    prior_subset := hFs
    prior_cover := hFc
    flagDeletions := L
    flag_monotone := hLm
    flag_subset := hLs
    flag_cover := hLc }⟩

end CircleDomainRigidity

end

end OAI
