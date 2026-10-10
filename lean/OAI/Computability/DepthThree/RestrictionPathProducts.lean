import OAI.Computability.DepthThree.RestrictionExpansion
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

universe u v

variable {V : Type u} {I : Type v} [DecidableEq V] [DecidableEq I] [Fintype I]

theorem pathDenominator_eq_prod_prefix (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) :
    pathDenominator scope T b violation P =
      ∏ h : Fin P.length,
        (easyCount scope T b violation (revealed scope T (P.take (h.val + 1))) : ℝ) := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih =>
      rw [pathDenominator_snoc, ih]
      rw [Fin.prod_univ_eq_prod_range
        (fun h : ℕ => (easyCount scope T b violation
          (revealed scope T (P.take (h + 1))) : ℝ)) P.length,
        Fin.prod_univ_eq_prod_range
          (fun h : ℕ => (easyCount scope T b violation
            (revealed scope T ((P ++ [i]).take (h + 1))) : ℝ)) (P ++ [i]).length]
      simp only [List.length_append, List.length_singleton, Finset.prod_range_succ]
      have hlast : (P ++ [i]).take (P.length + 1) = P ++ [i] :=
        List.take_of_length_le (by simp)
      rw [hlast]
      congr 1
      apply Finset.prod_congr rfl
      intro h hh
      rw [List.take_append_of_le_length
        (Nat.succ_le_of_lt (Finset.mem_range.mp hh))]

theorem pathNumerator_eq_indicator_support (violation : I → Bool) (P : List I) :
    pathNumerator violation P = if ∀ i ∈ P, violation i = true then 1 else 0 := by
  classical
  by_cases hs : ∀ i ∈ P, violation i = true
  · rw [ite_eq_left hs]
    unfold pathNumerator
    apply List.prod_eq_one
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    simp [violationValue, hs i hi]
  · rw [ite_eq_right hs]
    by_contra hne
    exact hs ((pathNumerator_ne_zero_iff violation P).mp hne)

theorem pathTerm_eq_support_prod_inv (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) :
    pathTerm scope T b violation P =
      if ∀ i ∈ P, violation i = true then
        ∏ h : Fin P.length,
          (easyCount scope T b violation
            (revealed scope T (P.take (h.val + 1))) : ℝ)⁻¹
      else 0 := by
  classical
  by_cases hs : ∀ i ∈ P, violation i = true
  · simp only [pathTerm, pathNumerator_eq_indicator_support, ite_eq_left hs,
      pathDenominator_eq_prod_prefix, one_div, Finset.prod_inv_distrib]
  · simp only [pathTerm, pathNumerator_eq_indicator_support, ite_eq_right hs, zero_div]

end DepthThreeLowerBound

end

end OAI
