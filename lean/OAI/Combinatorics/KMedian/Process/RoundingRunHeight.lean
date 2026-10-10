import Mathlib
import OAI.Combinatorics.KMedian.Process.RoundingCoordinateHeight
import OAI.Combinatorics.KMedian.Sparse.SparseIterationHeight

namespace OAI


                                         
section
namespace MetricKMedian.RoundingHeight
open RationalWeightedStep Binary
variable {n : ℕ}

theorem weighted_endpoint (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseWeightedPartial.run β hβ p t).length)
    (b : Fin 2) (i : Fin n) :
    HasHeight (point (endpoint β (SparseWeightedPartial.run β hβ p t).states[a.val] b) i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact endpoint_grid β hβ _ (initial_grid β p).1 _
      (SparseWeightedPartial.run_grid β hβ p _ (initial_grid β p).1 (initial_grid β p).2 t a) b
  · intro j hj; exact False.elim ((hβ j).ne' hj)
  · exact endpoint_feasible β hβ _ (SparseWeightedPartial.run_invariants β hβ p hu t a).1 b

theorem signed_endpoint (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseSignedPartial.run β p t).length)
    (b : Fin 2) (i : Fin n) :
    HasHeight (point (RationalSignedStep.endpoint β (SparseSignedPartial.run β p t).states[a.val] b) i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact RationalSignedStep.endpoint_grid β _ (initial_grid β p).1 _
      (SparseSignedPartial.run_grid β p _ (initial_grid β p).1 (initial_grid β p).2 t a) b
  · intro j hj
    exact (RationalSignedStep.endpoint_zero_weight β _ b j hj).trans
      (SparseSignedPartial.run_zero_weight β p t a j hj)
  · exact RationalSignedStep.endpoint_feasible β _ (SparseSignedPartial.run_invariants β p hu t a).1 b

def stepHeight (n L : ℕ) := SparseIntegerLaw.stepHeight (n+n*n+1) (n+n*n)
  (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L))

theorem weighted_denominator (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) :
    (SparseWeightedPartial.run β hβ p t).law.denominator≤(2:ℤ)^(stepHeight n L*t) := by
  induction t with
  | zero => simp only [SparseWeightedPartial.run,SparseIntegerLaw.dirac,mul_zero,pow_zero,le_refl]
  | succ t ih =>
    apply (SparseIntegerLaw.step_denominator_height _ _ _ _ _ (n+n*n+1)
      (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L)) (SparseWeightedPartial.run_length β hβ p t)
      (fun a => probability_height β _ _ L hb (weighted_run β hβ p L t hb hp hu a))
      (fun a b i => SparseWeightedPartial.features_height _ _ (weighted_endpoint β hβ p L t hb hp hu a b) i)).trans
    calc
      _ ≤ (2:ℤ)^(stepHeight n L*t)*(2:ℤ)^(stepHeight n L) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by rw [← pow_add,Nat.mul_succ]

theorem signed_denominator (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) :
    (SparseSignedPartial.run β p t).law.denominator≤(2:ℤ)^(stepHeight n L*t) := by
  induction t with
  | zero => simp only [SparseSignedPartial.run,SparseIntegerLaw.dirac,mul_zero,pow_zero,le_refl]
  | succ t ih =>
    apply (SparseIntegerLaw.step_denominator_height _ _ _ _ _ (n+n*n+1)
      (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L)) (SparseSignedPartial.run_length β p t)
      (fun a => RationalSignedStep.probability_height β _ _ L hb (signed_run β p L t hb hp hu a))
      (fun a b i => SparseWeightedPartial.features_height _ _ (signed_endpoint β p L t hb hp hu a b) i)).trans
    calc
      _ ≤ (2:ℤ)^(stepHeight n L*t)*(2:ℤ)^(stepHeight n L) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by rw [← pow_add,Nat.mul_succ]

end MetricKMedian.RoundingHeight
end

end OAI
