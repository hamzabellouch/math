import OAI.Combinatorics.ContingencyTables.Transport.ListedDenseDraw
import OAI.Combinatorics.ContingencyTables.Transport.CompletionDecisionReindex

namespace OAI

/-! # The computed large rectangle implements the reference decision -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] referenceFibreEquiv listedFibreEquiv
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "R₀" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P₀" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

lemma listedReferenceIndex_none (v : Fin m → ℕ) (V : ℕ)
    (hv : 0 < (largeIndices (V,List.ofFn v)).length) :
    listedReferenceIndex v V hv none=none :=
  Equiv.optionSubtypeNe_symm_self _

lemma listed_between (x y : PaperStates r c) (i) (j) :
    between (R x) (R y) (P x) (P y) i j=
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y)
        (listedReferenceIndex r (d^20) hr i) (listedReferenceIndex c (d^20) hc j) := by
  have he := between_reindex (listedReferenceIndex r (d^20) hr)
    (listedReferenceIndex c (d^20) hc)
    (listedReferenceIndex_none r _ hr) (listedReferenceIndex_none c _ hc)
    (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j
  simpa only [listedReference_row,listedReference_column] using he

lemma listed_translated_nonnegative (x y : PaperStates r c) (A : PaperFibre r c x) :
    (∀ i j,0 ≤ ((paperListedEquiv r c hr hc x A).val i j:ℤ)+
      between (R x) (R y) (P x) (P y) i j) ↔
    ∀ i j,0 ≤ ((paperReferenceEquiv r c i₀ j₀ x A).val i j:ℤ)+
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j := by
  have he (i) (j) : (paperListedEquiv r c hr hc x A).val i j=
      (paperReferenceEquiv r c i₀ j₀ x A).val
        (listedReferenceIndex r (d^20) hr i) (listedReferenceIndex c (d^20) hc j) :=
    @listedFibreEquiv_entry m n r c (d^20) (d^12) (stateCapacity r c) hr hc x
      (physical_paper_capacity (paperSmall r c) r c d (d^12) (d^20)
        dimension_le_allowance x) A i j
  simp only [he,listed_between]
  constructor
  · intro h i j
    obtain ⟨i,rfl⟩ := (listedReferenceIndex r (d^20) hr).surjective i
    obtain ⟨j,rfl⟩ := (listedReferenceIndex c (d^20) hc).surjective j
    exact h i j
  · intro h i j
    exact h _ _

theorem listed_completionDecision (x : PaperStates r c) (proposal : Option (PaperStates r c))
    (A : PaperFibre r c x) :
    completionDecision R P x proposal (paperListedEquiv r c hr hc x A)=
      completionDecision R₀ P₀ x proposal (paperReferenceEquiv r c i₀ j₀ x A) := by
  cases proposal with
  | none => rfl
  | some y =>
    unfold completionDecision
    dsimp only
    have he := listed_translated_nonnegative r c hr hc x y A
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (he.mp h₁))
    · exact False.elim (h₁ (he.mpr h₂))
    · rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
