import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite-dimensional algebra for the finite-strip construction.
The image estimate and algebraic injectivity step do not require
the analytic mass inequality. -/

namespace SymmetricMahler

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Apply the real matrix whose rows encode the strip constraints. -/
def measurement (A : J → I → ℝ) (v : I → ℝ) (j : J) : ℝ := ∑ i, A j i * v i

/-- Apply the transpose of the strip matrix to a vector of coefficients. -/
def push (A : J → I → ℝ) (p : J → ℝ) (i : I) : ℝ := ∑ j, A j i * p j

def stripBody (A : J → I → ℝ) : Set (I → ℝ) :=
  {v | ∀ j, |measurement A v j| ≤ 1}

/-- The transpose identity in the image bound. -/
theorem transpose_pairing (A : J → I → ℝ) (p : J → ℝ) (v : I → ℝ) :
    (∑ i, push A p i * v i) = ∑ j, p j * measurement A v j := by
  simp only [push, measurement, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

/-- Coefficients with bounded l1 norm define a bounded polar functional. -/
theorem image_bound (A : J → I → ℝ) (p : J → ℝ) (v : I → ℝ)
    (hv : v ∈ stripBody A) :
    (∑ i, push A p i * v i) ≤ ∑ j, |p j| := by
  rw [transpose_pairing]
  apply sum_le_sum
  intro j _
  calc
    p j * measurement A v j ≤ |p j * measurement A v j| := le_abs_self _
    _ = |p j| * |measurement A v j| := abs_mul _ _
    _ ≤ |p j| * 1 := mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = |p j| := mul_one _

/-- The scalar strict-monotonicity argument needs no derivative assumption. -/
theorem monotone_product_nonneg {f : ℝ → ℝ} (hf : StrictMono f) (a b : ℝ) :
    0 ≤ (f a - f b) * (a - b) := by
  rcases le_total a b with hab | hba
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf.monotone hab))
      (sub_nonpos.mpr hab)
  · exact mul_nonneg (sub_nonneg.mpr (hf.monotone hba)) (sub_nonneg.mpr hba)

theorem monotone_product_pos {f : ℝ → ℝ} (hf : StrictMono f) {a b : ℝ}
    (hab : a ≠ b) : 0 < (f a - f b) * (a - b) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hf hab)) (sub_neg.mpr hab)
  · exact mul_pos (sub_pos.mpr (hf hba)) (sub_pos.mpr hba)

/-- The positive sum in the injectivity argument. -/
theorem strict_pairing (A : J → I → ℝ)
    (hA : Function.Injective (measurement A))
    (f : J → ℝ → ℝ) (hf : ∀ j, StrictMono (f j))
    {y y' : I → ℝ} (hy : y ≠ y') :
    0 < ∑ j, (f j (measurement A y j) - f j (measurement A y' j)) *
      (measurement A y j - measurement A y' j) := by
  classical
  have hdiff : measurement A y ≠ measurement A y' := fun h => hy (hA h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hdiff
  apply sum_pos'
  · intro k _
    exact monotone_product_nonneg (hf k) _ _
  · exact ⟨j, mem_univ j, monotone_product_pos (hf j) hj⟩

/-- Injectivity of the vertical map `y ↦ Aᵀ (P_j ((Ay)_j))`.
This is the algebraic injectivity step for the finite-strip construction. -/
theorem vertical_map_injective (A : J → I → ℝ)
    (hA : Function.Injective (measurement A))
    (f : J → ℝ → ℝ) (hf : ∀ j, StrictMono (f j)) :
    Function.Injective (fun y : I → ℝ => push A (fun j => f j (measurement A y j))) := by
  classical
  intro y y' h
  by_contra hne
  have hp := strict_pairing A hA f hf hne
  have hz : (∑ i, push A (fun j => f j (measurement A y j) -
      f j (measurement A y' j)) i * (y i - y' i)) = 0 := by
    apply sum_eq_zero
    intro i _
    have hi := congrFun h i
    simp only [push] at hi ⊢
    rw [show (∑ j, A j i * (f j (measurement A y j) - f j (measurement A y' j))) =
        (∑ j, A j i * f j (measurement A y j)) -
        (∑ j, A j i * f j (measurement A y' j)) by
      simp only [mul_sub, sum_sub_distrib]]
    rw [hi, sub_self, zero_mul]
  rw [transpose_pairing] at hz
  have hmeasurement : ∀ j, measurement A (fun i => y i - y' i) j =
      measurement A y j - measurement A y' j := by
    intro j
    simp only [measurement, mul_sub, sum_sub_distrib]
  simp only [hmeasurement] at hz
  linarith

end SymmetricMahler

namespace SymmetricMahler

open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The relevant vertical fibers need only support strict monotonicity on
an interval, rather than on all of the real line. -/
theorem vertical_map_injOn (A : J → I → ℝ)
    (hA : Function.Injective (measurement A))
    (S : J → Set ℝ) (f : J → ℝ → ℝ)
    (hf : ∀ j, StrictMonoOn (f j) (S j)) :
    Set.InjOn (fun y : I → ℝ => push A (fun j => f j (measurement A y j)))
      {y | ∀ j, measurement A y j ∈ S j} := by
  classical
  intro y hy y' hy' hout
  by_contra hne
  have hnonneg : ∀ j, 0 ≤ (f j (measurement A y j) - f j (measurement A y' j)) *
      (measurement A y j - measurement A y' j) := by
    intro j
    rcases le_total (measurement A y j) (measurement A y' j) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr ((hf j).monotoneOn (hy j) (hy' j) h)) (sub_nonpos.mpr h)
    · exact mul_nonneg
        (sub_nonneg.mpr ((hf j).monotoneOn (hy' j) (hy j) h)) (sub_nonneg.mpr h)
  have hdiff : measurement A y ≠ measurement A y' := fun h => hne (hA h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hdiff
  have hpos : 0 < (f j (measurement A y j) - f j (measurement A y' j)) *
      (measurement A y j - measurement A y' j) := by
    rcases lt_or_gt_of_ne hj with h | h
    · exact mul_pos_of_neg_of_neg
        (sub_neg.mpr (hf j (hy j) (hy' j) h)) (sub_neg.mpr h)
    · exact mul_pos (sub_pos.mpr (hf j (hy' j) (hy j) h)) (sub_pos.mpr h)
  have hp : 0 < ∑ k, (f k (measurement A y k) - f k (measurement A y' k)) *
      (measurement A y k - measurement A y' k) :=
    sum_pos' (fun k _ => hnonneg k) ⟨j, mem_univ j, hpos⟩
  have hz : (∑ i, push A (fun k => f k (measurement A y k) -
      f k (measurement A y' k)) i * (y i - y' i)) = 0 := by
    apply sum_eq_zero
    intro i _
    have hi := congrFun hout i
    simp only [push] at hi ⊢
    simp only [mul_sub, sum_sub_distrib, hi, sub_self, zero_mul]
  rw [transpose_pairing] at hz
  have hmeasurement : ∀ k, measurement A (fun i => y i - y' i) k =
      measurement A y k - measurement A y' k := by
    intro k
    simp only [measurement, mul_sub, sum_sub_distrib]
  simp only [hmeasurement] at hz
  linarith

/-- The full real map is injective when each vertical slice satisfies the
hypotheses proved above. This also permits the fiber interval to depend on x. -/
theorem full_map_injOn (A : J → I → ℝ)
    (hA : Function.Injective (measurement A))
    (S : (I → ℝ) → J → Set ℝ) (f : (I → ℝ) → J → ℝ → ℝ)
    (hf : ∀ x j, StrictMonoOn (f x j) (S x j)) :
    Set.InjOn
      (fun z : (I → ℝ) × (I → ℝ) =>
        (z.1, push A (fun j => f z.1 j (measurement A z.2 j))))
      {z | ∀ j, measurement A z.2 j ∈ S z.1 j} := by
  intro z hz w hw h
  have hx : z.1 = w.1 := by
    simpa only using congrArg (fun q : (I → ℝ) × (I → ℝ) => q.1) h
  change ∀ j, measurement A z.2 j ∈ S z.1 j at hz
  change ∀ j, measurement A w.2 j ∈ S w.1 j at hw
  have hv : push A (fun j => f z.1 j (measurement A z.2 j)) =
      push A (fun j => f z.1 j (measurement A w.2 j)) := by
    simpa only [hx] using congrArg Prod.snd h
  have hy := vertical_map_injOn A hA (S z.1) (f z.1) (hf z.1) hz
    (by simpa only [Set.mem_ofPred_eq, hx] using hw) hv
  exact Prod.ext hx hy

/-- The planar uniform error accumulates only by the number of rows. -/
theorem coefficient_bound (p t : J → ℝ) (ε : ℝ)
    (hp : ∀ j, |p j| ≤ t j + ε) (ht : (∑ j, t j) < 1) :
    (∑ j, |p j|) < 1 + Fintype.card J * ε := by
  calc
    (∑ j, |p j|) ≤ ∑ j, (t j + ε) := sum_le_sum (fun j _ => hp j)
    _ = (∑ j, t j) + Fintype.card J * ε := by simp [sum_add_distrib]
    _ < 1 + Fintype.card J * ε := by linarith

/-- The pointwise image estimate, including the planar error. -/
theorem image_bound_with_error (A : J → I → ℝ) (p t : J → ℝ) (ε : ℝ)
    (hp : ∀ j, |p j| ≤ t j + ε) (ht : (∑ j, t j) < 1)
    (v : I → ℝ) (hv : v ∈ stripBody A) :
    (∑ i, push A p i * v i) < 1 + Fintype.card J * ε :=
  lt_of_le_of_lt (image_bound A p v hv) (coefficient_bound p t ε hp ht)

end SymmetricMahler

end OAI
