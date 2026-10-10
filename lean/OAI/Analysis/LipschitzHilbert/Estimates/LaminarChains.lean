import OAI.Analysis.LipschitzHilbert.Estimates.CarlesonSorting
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Iterated Carleson sums for a finite laminar family

The family is indexed by occurrences, so equal geometric intervals from
different bins retain their multiplicity. Iterating the actual Carleson
mass bound controls every non-strict nested-chain sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def tupleIntersection (Q : ι → Set X) {n : ℕ} (P : Set X) (a : Fin n → ι) : Set X :=
  P ∩ ⋂ j, Q (a j)

def laminarChainWeight (Q : ι → Set X) (μ : Measure X) :
    (n : ℕ) → Set X → (Fin n → ι) → ℝ
  | 0, P, _ => μ.real P
  | n + 1, P, a => if Q (a 0) ⊆ P then
      laminarChainWeight Q μ n (Q (a 0)) (fun j => a j.succ) else 0

omit [Fintype ι] in
theorem laminarChainWeight_nonneg (Q : ι → Set X) (μ : Measure X)
    (n : ℕ) (P : Set X) (a : Fin n → ι) : 0 ≤ laminarChainWeight Q μ n P a := by
  induction n generalizing P with
  | zero => exact measureReal_nonneg
  | succ n ih =>
    simp only [laminarChainWeight]
    split_ifs
    · exact ih _ _
    · exact le_rfl

def tupleHeadTailEquiv (n : ℕ) : (Fin (n + 1) → ι) ≃ ι × (Fin n → ι) where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by funext j; refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  right_inv p := by rcases p with ⟨i, a⟩; rfl

theorem sum_laminarChainWeight_succ (Q : ι → Set X) (μ : Measure X)
    (n : ℕ) (P : Set X) :
    (∑ a : Fin (n + 1) → ι, laminarChainWeight Q μ (n + 1) P a) =
      ∑ i : ι, if Q i ⊆ P then ∑ a : Fin n → ι, laminarChainWeight Q μ n (Q i) a else 0 := by
  trans ∑ p : ι × (Fin n → ι),
    if Q p.1 ⊆ P then laminarChainWeight Q μ n (Q p.1) p.2 else 0
  · exact Fintype.sum_equiv (tupleHeadTailEquiv n) _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- The second inequality of `count:moment`, with repeated intervals allowed. -/
theorem sum_laminarChainWeight_le (Q : ι → Set X) (μ : Measure X) (P₀ : Set X)
    {A : ℝ} (hA : 0 ≤ A)
    (hcarleson : ∀ P, P = P₀ ∨ P ∈ Set.range Q →
      (∑ i, if Q i ⊆ P then μ.real (Q i) else 0) ≤ A * μ.real P)
    (n : ℕ) {P : Set X} (hP : P = P₀ ∨ P ∈ Set.range Q) :
    (∑ a : Fin n → ι, laminarChainWeight Q μ n P a) ≤ A ^ n * μ.real P := by
  induction n generalizing P with
  | zero => simp [laminarChainWeight]
  | succ n ih =>
    rw [sum_laminarChainWeight_succ]
    calc
      (∑ i, if Q i ⊆ P then ∑ a : Fin n → ι, laminarChainWeight Q μ n (Q i) a else 0) ≤
          ∑ i, if Q i ⊆ P then A ^ n * μ.real (Q i) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact ih (Or.inr ⟨i, rfl⟩)
        · exact le_rfl
      _ = A ^ n * ∑ i, if Q i ⊆ P then μ.real (Q i) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ ≤ A ^ n * (A * μ.real P) :=
        mul_le_mul_of_nonneg_left (hcarleson P hP) (pow_nonneg hA n)
      _ = A ^ (n + 1) * μ.real P := by rw [pow_succ]; ring

omit [Fintype ι] [MeasurableSpace X] in
theorem tupleIntersection_succ (Q : ι → Set X) {n : ℕ} (P : Set X)
    (a : Fin (n + 1) → ι) (hhead : Q (a 0) ⊆ P) :
    tupleIntersection Q P a = tupleIntersection Q (Q (a 0)) (fun j => a j.succ) := by
  ext x
  simp only [tupleIntersection, Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_succ]
  exact ⟨fun hx => ⟨hx.2.1, hx.2.2⟩,
    fun hx => ⟨hhead hx.1, hx.1, hx.2⟩⟩

omit [Fintype ι] in
theorem laminarChainWeight_eq_intersection (Q : ι → Set X) (μ : Measure X)
    (n : ℕ) (P : Set X) (a : Fin n → ι)
    (hsub : ∀ j, Q (a j) ⊆ P)
    (hnested : ∀ i j, i ≤ j → Q (a j) ⊆ Q (a i)) :
    laminarChainWeight Q μ n P a = μ.real (tupleIntersection Q P a) := by
  induction n generalizing P with
  | zero => simp [laminarChainWeight, tupleIntersection]
  | succ n ih =>
    rw [laminarChainWeight, ite_eq_left (hsub 0), tupleIntersection_succ Q P a (hsub 0)]
    apply ih
    · intro j
      exact hnested 0 j.succ (Fin.zero_le _)
    · intro i j hij
      exact hnested i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)

omit [Fintype ι] in
/-- Monotonicity of the scale rank turns every nonempty intersection into
an actual nested chain; empty intersections contribute zero. -/
theorem sorted_intersection_mass_le_chain (Q : ι → Set X) (μ : Measure X)
    (rank : ι → ℤ)
    (horder : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (n : ℕ) (P : Set X) (a : Fin n → ι) (hsub : ∀ j, Q (a j) ⊆ P)
    (hsorted : Antitone (rank ∘ a)) :
    μ.real (tupleIntersection Q P a) ≤ laminarChainWeight Q μ n P a := by
  by_cases hnonempty : (tupleIntersection Q P a).Nonempty
  · obtain ⟨x, hx⟩ := hnonempty
    have hnested : ∀ i j, i ≤ j → Q (a j) ⊆ Q (a i) := by
      intro i j hij
      apply horder _ _ (hsorted hij)
      exact ⟨x, Set.mem_iInter.mp hx.2 i, Set.mem_iInter.mp hx.2 j⟩
    rw [laminarChainWeight_eq_intersection Q μ n P a hsub hnested]
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, measureReal_empty]
    exact laminarChainWeight_nonneg Q μ n P a

end LipschitzHilbert

end

end OAI
