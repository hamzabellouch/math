import OAI.Analysis.LipschitzHilbert.Estimates.LaminarChains
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-!
# Factorial moments of a finite laminar count

This proves equation `count:moment` of §6. The hypotheses are the actual
Carleson mass bound on the root and selected intervals and the geometric
ordering of intersecting intervals by their scale.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def laminarCount (Q : ι → Set X) (x : X) : ℝ := ∑ i, (Q i).indicator 1 x

theorem measurable_laminarCount (Q : ι → Set X) (hQ : ∀ i, MeasurableSet (Q i)) :
    Measurable (laminarCount Q) := by
  unfold laminarCount
  exact Finset.measurable_sum _ fun i _ => measurable_one.indicator (hQ i)

omit [MeasurableSpace X] in
theorem laminarCount_nonneg (Q : ι → Set X) (x : X) : 0 ≤ laminarCount Q x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]

omit [MeasurableSpace X] in
theorem laminarCount_le_card (Q : ι → Set X) (x : X) :
    laminarCount Q x ≤ (Fintype.card ι : ℝ) := by
  calc
    laminarCount Q x ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hx : x ∈ Q i <;> simp [Set.indicator, hx]
    _ = _ := by simp

omit [Fintype ι] [MeasurableSpace X] in
theorem tupleIntersection_comp_perm (Q : ι → Set X) {n : ℕ} (P : Set X)
    (a : Fin n → ι) (σ : Equiv.Perm (Fin n)) :
    tupleIntersection Q P (a ∘ σ) = tupleIntersection Q P a := by
  ext x
  simp only [tupleIntersection, Set.mem_inter_iff, Set.mem_iInter, Function.comp_apply]
  constructor
  · intro hx
    refine ⟨hx.1, fun j => ?_⟩
    simpa only [σ.apply_symm_apply] using hx.2 (σ.symm j)
  · intro hx
    exact ⟨hx.1, fun j => hx.2 (σ j)⟩

omit [Fintype ι] [MeasurableSpace X] in
theorem product_indicators_eq_tuple_indicator (Q : ι → Set X) {n : ℕ} (a : Fin n → ι) :
    (fun x => ∏ j, (Q (a j)).indicator (1 : X → ℝ) x) =
      (⋂ j, Q (a j)).indicator 1 := by
  funext x
  simpa using
    prod_indicator_apply Finset.univ (fun j => Q (a j)) (fun _ => (1 : X → ℝ)) x

theorem integral_laminarCount_pow (Q : ι → Set X) (μ : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i)) {P : Set X} (hPfinite : μ P ≠ ⊤) (n : ℕ) :
    (∫ x in P, laminarCount Q x ^ n ∂μ) =
      ∑ a : Fin n → ι, μ.real (tupleIntersection Q P a) := by
  have : IsFiniteMeasure (μ.restrict P) := isFiniteMeasure_restrict.mpr hPfinite
  have hmeas (a : Fin n → ι) : MeasurableSet (⋂ j, Q (a j)) := MeasurableSet.iInter (fun _ => hQ _)
  have hint (a : Fin n → ι) :
      Integrable (fun x => ∏ j, (Q (a j)).indicator (1 : X → ℝ) x) (μ.restrict P) := by
    rw [product_indicators_eq_tuple_indicator]
    exact (integrable_const (1 : ℝ)).indicator (hmeas a)
  simp only [laminarCount, Fintype.sum_pow]
  rw [integral_finsetSum _ (fun a _ => hint a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [product_indicators_eq_tuple_indicator, integral_indicator_one (hmeas a),
    measureReal_restrict_apply (hmeas a)]
  simp only [tupleIntersection, Set.inter_comm]

/-- The finite laminar Carleson moment bound, with exact factorial constant. -/
theorem laminar_count_moment (Q : ι → Set X) (μ : Measure X) (rank : ι → ℤ)
    (hQ : ∀ i, MeasurableSet (Q i)) {P₀ : Set X} (hPfinite : μ P₀ ≠ ⊤)
    (hsub : ∀ i, Q i ⊆ P₀)
    (horder : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    {A : ℝ} (hA : 0 ≤ A)
    (hcarleson : ∀ P, P = P₀ ∨ P ∈ Set.range Q →
      (∑ i, if Q i ⊆ P then μ.real (Q i) else 0) ≤ A * μ.real P)
    (n : ℕ) :
    (∫ x in P₀, laminarCount Q x ^ n ∂μ) ≤
      (n.factorial : ℝ) * A ^ n * μ.real P₀ := by
  rw [integral_laminarCount_pow Q μ hQ hPfinite]
  have hsort := sum_tuple_le_factorial_sum_sorted (fun i => -rank i) n
    (fun a => μ.real (tupleIntersection Q P₀ a)) (fun _ => measureReal_nonneg)
    (fun a σ => congrArg (μ.real) (tupleIntersection_comp_perm Q P₀ a σ))
  apply hsort.trans
  calc
    (n.factorial : ℝ) * ∑ a : Fin n → ι,
        (if Monotone (fun j => -rank (a j)) then μ.real (tupleIntersection Q P₀ a) else 0) ≤
      (n.factorial : ℝ) * ∑ a : Fin n → ι, laminarChainWeight Q μ n P₀ a := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro a _
      split_ifs with hs
      · have hs' : Antitone (rank ∘ a) := by
          intro i j hij
          have hh := hs hij
          exact neg_le_neg_iff.mp hh
        exact sorted_intersection_mass_le_chain Q μ rank horder n P₀ a (fun j => hsub (a j)) hs'
      · exact laminarChainWeight_nonneg Q μ n P₀ a
    _ ≤ (n.factorial : ℝ) * (A ^ n * μ.real P₀) :=
      mul_le_mul_of_nonneg_left (sum_laminarChainWeight_le Q μ P₀ hA hcarleson n (Or.inl rfl))
        (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
