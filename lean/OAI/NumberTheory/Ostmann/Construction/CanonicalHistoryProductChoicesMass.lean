import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoices

namespace OAI

noncomputable section
namespace Ostmann.Construction
open CanonicalOccurrenceTransport
open scoped BigOperators

theorem choicesMass_eq_source_product (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (c : HistoryChoices sources seed V l) :
    choicesMass sources seed V l c =
      ∏ i : Internal seed l,
        (sources (internalSource seed i).origin).law.mass (historyDraws sources seed V l c i) := by
  induction l with
  | zero => simp only [choicesMass,Internal,Finset.univ_eq_empty,Finset.prod_empty]
  | succ l ih =>
    rw [choicesMass]
    change _ = ∏ i : Fin (Template.extracted (l+1) (Template.current seed l)).length ⊕
      (Internal seed l ⊕ Internal seed l), _
    rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
    simp only [internalSource,historyDraws,←ih,assignmentPrior,dependentProductPrior,List.get_eq_getElem]
    exact mul_assoc _ _ _

theorem choicesMass_eq_internalSourcePrior (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (c : HistoryChoices sources seed V l) :
    choicesMass sources seed V l c =
      (internalSourcePrior sources seed l).mass (historyDraws sources seed V l c) :=
  choicesMass_eq_source_product sources seed V l c

@[simp] theorem choicesMass_assemble (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (f : FrequencyChoices V l) (x : InternalSourceDraws sources seed l) :
    choicesMass sources seed V l (assembleHistoryChoices sources seed V l f x)=
      (internalSourcePrior sources seed l).mass x := by
  rw [choicesMass_eq_internalSourcePrior,historyDraws_assemble]

theorem sum_choicesMass_eq_source_prior (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (F : HistoryChoices sources seed V l → ℂ) :
    (∑ c : HistoryChoices sources seed V l,(choicesMass sources seed V l c:ℂ)*F c) =
      ∑ f : FrequencyChoices V l,∑ x : InternalSourceDraws sources seed l,
        ((internalSourcePrior sources seed l).mass x:ℂ)*
          F (assembleHistoryChoices sources seed V l f x) := by
  rw [sum_historyChoices_eq]
  simp only [choicesMass_assemble]

theorem sum_choicesMass_eq_source_prior_real (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (F : HistoryChoices sources seed V l → ℝ) :
    (∑ c : HistoryChoices sources seed V l,choicesMass sources seed V l c*F c) =
      ∑ f : FrequencyChoices V l,∑ x : InternalSourceDraws sources seed l,
        (internalSourcePrior sources seed l).mass x*
          F (assembleHistoryChoices sources seed V l f x) := by
  rw [sum_historyChoices_eq]
  simp only [choicesMass_assemble]

end Ostmann.Construction

end

end OAI
