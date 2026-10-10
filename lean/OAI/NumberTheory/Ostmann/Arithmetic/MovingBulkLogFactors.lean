import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogWeight
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSmoothRootCuts

namespace OAI

/-! # The retained bulk logarithmic cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkLogCutoffWeight {σ : Type*} (value : σ → ℝ)
    (cb : ℝ) (slots : List σ) : ℝ :=
  positiveLogCutoff logCellProfile cb (realSlotProduct value slots)

theorem bulkLogCutoffWeight_bounds {σ : Type*} (value : σ → ℝ)
    (cb : ℝ) (slots : List σ) :
    0 ≤ bulkLogCutoffWeight value cb slots ∧ bulkLogCutoffWeight value cb slots ≤ 1 := by
  unfold bulkLogCutoffWeight positiveLogCutoff
  split_ifs
  · exact ⟨logCellProfile_nonneg _, logCellProfile_le_one _⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- At the original positive prime values this is precisely the initial
log-sum cutoff, including its unchanged spectator factor. -/
theorem movingBulkListLogWeight_eq_cutoff {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ a, 0 < value a) (outside : List ℕ) (cb cd : ℝ) (slots : List σ) :
    movingBulkListLogWeight value outside cb cd slots =
      bulkLogCutoffWeight (fun a => (value a : ℝ)) cb slots *
        logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) := by
  have hp : 0 < realSlotProduct (fun a => (value a : ℝ)) slots := by
    unfold realSlotProduct
    apply List.prod_pos
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact_mod_cast hvalue a
  have hl : Real.log (realSlotProduct (fun a => (value a : ℝ)) slots) =
      (slots.map (fun a => Real.log (value a : ℝ))).sum := by
    unfold realSlotProduct
    rw [Real.log_list_prod]
    · simp only [List.map_map, Function.comp_def]
    · intro x hx
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hvalue a))
  simp only [movingBulkListLogWeight, bulkLogCutoffWeight, positiveLogCutoff,
    ite_eq_left hp, hl]

noncomputable def bulkLogCutoffFactors {σ : Type*} {t : ℕ}
    (value : σ → ℝ) (i : σ) (cb D : ℝ) (hD : 0 ≤ D)
    (hlip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y|)
    (slots : Fin t → List σ) : Fin t → ClippedPolynomialFactor := fun j =>
  logCutoffPolynomialFactor (bulkSlotProduct value i (slots j)) logCellProfile cb 1 D
    zero_le_one hD (fun x => by
      rw [abs_of_nonneg (logCellProfile_nonneg x)]
      exact logCellProfile_le_one x) hlip

theorem bulkLogCutoffFactors_weight {σ : Type*} {t : ℕ}
    (value : σ → ℝ) (i : σ) (cb D : ℝ) (hD : 0 ≤ D)
    (hlip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y|)
    (slots : Fin t → List σ) (z : ℝ) :
    smoothPolynomialWeight (bulkLogCutoffFactors value i cb D hD hlip slots) z =
      ((∏ j, bulkLogCutoffWeight (Function.update value i z) cb (slots j) : ℝ) : ℂ) := by
  simp only [smoothPolynomialWeight, bulkLogCutoffFactors, bulkLogCutoffWeight,
    Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [logCutoffPolynomialFactor_value (hout := logCellProfile_zero_outside),
    bulkSlotProduct_eval]

theorem bulkLogCutoffFactors_budget {σ : Type*} {t : ℕ}
    (value : σ → ℝ) (i : σ) (cb D : ℝ) (hD : 0 ≤ D)
    (hlip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y|)
    (slots : Fin t → List σ) :
    smoothPolynomialBudget (bulkLogCutoffFactors value i cb D hD hlip slots) =
      (2 + D * (Real.exp 2 - 1)) ^ t := by
  simp only [smoothPolynomialBudget, bulkLogCutoffFactors, logCutoffPolynomialFactor_budget,
    mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Repeated occurrences in a leaf group are retained. They contribute their
actual multiplicity to the elementary degree bound. -/
theorem bulkLogCutoffFactors_roots {σ : Type*} {t : ℕ}
    (value : σ → ℝ) (i : σ) (cb D : ℝ) (hD : 0 ≤ D)
    (hlip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y|)
    (slots : Fin t → List σ) (r : ℕ) (hr : ∀ j, (slots j).length ≤ r) :
    ∃ S : Finset ℝ, S.card ≤ t * r ∧
      ∀ j z, z ∈ (bulkLogCutoffFactors value i cb D hD hlip slots j).polynomial.derivative.roots → z ∈ S := by
  let F := bulkLogCutoffFactors value i cb D hD hlip slots
  let S := polynomialRootCuts (fun j => (F j).polynomial.derivative)
  refine ⟨S, ?_, ?_⟩
  · apply (polynomialRootCuts_card _).trans
    calc
      _ ≤ ∑ _j : Fin t, r := Finset.sum_le_sum (fun j _ =>
        (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans
          ((bulkSlotProduct_degree value i (slots j)).trans (hr j))))
      _ = _ := by simp
  · intro j z hz
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hz⟩

end Ostmann

end OAI
