import OAI.Probability.DilutedSpin.RootPatternComparison

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n : ℕ}

lemma qExpect_sub (m : Fin (n+1) → ℝ) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T-G T) k S=qExpect m F k S-qExpect m G k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,mul_sub,Finset.sum_sub_distrib]

lemma abs_qExpect_le_qExpect_abs (m : Fin (n+1) → ℝ) (hm : Monotone m)
    (hpos : ∀ j, 0 ≤ m j) (F : PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    |qExpect m F k S| ≤ qExpect m (fun T => |F T|) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    unfold qExpect
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro v _
    have hcoef := div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg S.leaves)
    rw [abs_mul,abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left (ih (grow S v)) hcoef

lemma measurable_qExpect (m : Fin (n+1) → ℝ) (F : Z → PrescribedTree n → ℝ)
    (hF : ∀ T, Measurable (fun z => F z T)) (k : ℕ) (S : PrescribedTree n) :
    Measurable (fun z => qExpect m (F z) k S) := by
  induction k generalizing S with
  | zero => exact hF S
  | succ k ih => exact Finset.measurable_fun_sum _ (fun v _ => (ih (grow S v)).const_mul _)

lemma integrable_qExpect (μ : Measure Z) (m : Fin (n+1) → ℝ)
    (F : Z → PrescribedTree n → ℝ) (hF : ∀ T, Integrable (fun z => F z T) μ)
    (k : ℕ) (S : PrescribedTree n) : Integrable (fun z => qExpect m (F z) k S) μ := by
  induction k generalizing S with
  | zero => exact hF S
  | succ k ih => exact integrable_finsetSum _ (fun v _ => (ih (grow S v)).const_mul _)

lemma integral_qExpect (μ : Measure Z) (m : Fin (n+1) → ℝ)
    (F : Z → PrescribedTree n → ℝ) (hF : ∀ T, Integrable (fun z => F z T) μ)
    (k : ℕ) (S : PrescribedTree n) :
    (∫ z, qExpect m (F z) k S ∂μ) = qExpect m (fun T => ∫ z, F z T ∂μ) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect]
    rw [integral_finsetSum _ (fun v _ =>
      (integrable_qExpect μ m F hF k (grow S v)).const_mul _)]
    simp only [integral_const_mul,ih]

lemma qExpect_difference_bound (m : Fin (n+1) → ℝ) (hm : Monotone m)
    (hpos : ∀ j, 0 ≤ m j) (F G E : PrescribedTree n → ℝ)
    (h : ∀ S, |F S-G S|≤E S) (k : ℕ) (S : PrescribedTree n) :
    |qExpect m F k S-qExpect m G k S|≤qExpect m E k S := by
  rw [← qExpect_sub]
  exact (abs_qExpect_le_qExpect_abs m hm hpos _ k S).trans (qExpect_mono m hm hpos h k S)

end DilutedSpinGlass.PrescribedTree

end

end OAI
