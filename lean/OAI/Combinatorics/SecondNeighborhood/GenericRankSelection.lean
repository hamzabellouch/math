import OAI.Combinatorics.SecondNeighborhood.GenericRankGlobalMinors
import OAI.Combinatorics.SecondNeighborhood.GenericRankColumns

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite
open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem matrixL_supported_on_matchingSupport (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    ∀ z left, ¬ matrixLSupport r R C z left →
      matrixL r R C (selectedA r v) z left = 0 := by
  classical
  intro z left hs
  by_cases hc : z.1.2 = left.1.2
  · have hr : ¬ r left.1.1 z.1.1 := fun hr => hs ⟨hc, hr⟩
    simp [matrixL, selectedA, hc, hr]
  · simp [matrixL, hc]

theorem matrixNTranspose_supported_on_matchingSupport (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    ∀ z right, ¬ matrixNTransposeSupport r R C z right →
      (matrixN r R C (selectedB r v))ᵀ z right = 0 := by
  classical
  intro z right hs
  by_cases hc : right.1.1 = z.1.1
  · have hr : ¬ r right.1.2 z.1.2 := fun hr => hs ⟨hc, hr⟩
    simp [Matrix.transpose_apply, matrixN, selectedB, hc, hr]
  · simp [Matrix.transpose_apply, matrixN, hc]

theorem exists_pruning_rank_coefficients
    (r : X → X → Prop) (R C : Finset (X × X))
    (α : Finset (↥(Z r R C) × ↥R)) (β : Finset (↥(Z r R C) × ↥C))
    (hα : IsMaximumMatching (matrixLSupport r R C) α)
    (hβ : IsMaximumMatching (matrixNTransposeSupport r R C) β) :
    ∃ v : CoefficientVariables X → ℝ,
      SupportedCoefficients r (selectedA r v) ∧
      SupportedCoefficients r (selectedB r v) ∧
      LocalMaximalRanks r R C (selectedB r v) ∧
      ((matrixL r R C (selectedA r v)).submatrix
        (fun e : ↥α => e.1.1) (fun e : ↥α => e.1.2)).det ≠ 0 ∧
      (((matrixN r R C (selectedB r v))ᵀ).submatrix
        (fun e : ↥β => e.1.1) (fun e : ↥β => e.1.2)).det ≠ 0 ∧
      (matrixL r R C (selectedA r v)).rank = α.card ∧
      ((matrixN r R C (selectedB r v))ᵀ).rank = β.card := by
  classical
  let extra : Bool → MvPolynomial (CoefficientVariables X) ℝ := fun t =>
    if t then (matrixLMatchingMinor r R C α).det
    else (matrixNTransposeMatchingMinor r R C β).det
  have hextra : ∀ t, extra t ≠ 0 := by
    intro t
    cases t with
    | false => exact det_matrixNTransposeMatchingMinor_ne_zero r R C β hβ.1
    | true => exact det_matrixLMatchingMinor_ne_zero r R C α hα.1
  obtain ⟨v, hv, ha, hb, hlocal⟩ :=
    exists_coefficients_localMaximalRanks r R C extra hextra
  have hdetL : ((matrixL r R C (selectedA r v)).submatrix
      (fun e : ↥α => e.1.1) (fun e : ↥α => e.1.2)).det ≠ 0 := by
    have h := hv true
    change MvPolynomial.eval v (matrixLMatchingMinor r R C α).det ≠ 0 at h
    simpa only [← det_evalPolynomialMatrix, eval_matrixLMatchingMinor] using h
  have hdetN : (((matrixN r R C (selectedB r v))ᵀ).submatrix
      (fun e : ↥β => e.1.1) (fun e : ↥β => e.1.2)).det ≠ 0 := by
    have h := hv false
    change MvPolynomial.eval v (matrixNTransposeMatchingMinor r R C β).det ≠ 0 at h
    simpa only [← det_evalPolynomialMatrix, eval_matrixNTransposeMatchingMinor] using h
  refine ⟨v, ha, hb, hlocal, hdetL, hdetN, ?_, ?_⟩
  · exact rank_eq_card_of_maximum_matching_minor hα _
      (matrixL_supported_on_matchingSupport r R C v) hdetL
  · exact rank_eq_card_of_maximum_matching_minor hβ _
      (matrixNTranspose_supported_on_matchingSupport r R C v) hdetN

end SeymourSecondNeighborhood.Pruning

end OAI
