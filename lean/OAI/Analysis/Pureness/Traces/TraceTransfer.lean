import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
namespace CuntzPureness
open Finset

variable {A C ι : Type*} [Ring A] [StarRing A] [AddCommMonoid C]

def traceTransfer (I : Finset ι) (r p : A) (s : ι → A) : A :=
  ∑ i ∈ I, r * s i * p * star (s i) * r

theorem trace_transfer_identity (τ : A →+ C)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (I : Finset ι) (r p : A) (s : ι → A)
    (hfull : ∑ i ∈ I, star (s i) * (r * r) * s i = 1) :
    τ (traceTransfer I r p s) = τ p := by
  unfold traceTransfer
  rw [map_sum]
  calc
    (∑ i ∈ I, τ (r * s i * p * star (s i) * r)) =
        ∑ i ∈ I, τ ((star (s i) * (r * r) * s i) * p) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        τ (r * s i * p * star (s i) * r) =
            τ ((r * s i * p) * (star (s i) * r)) := by simp only [mul_assoc]
        _ = τ ((star (s i) * r) * (r * s i * p)) := hτ _ _
        _ = τ ((star (s i) * (r * r) * s i) * p) := by simp only [mul_assoc]
    _ = τ ((∑ i ∈ I, star (s i) * (r * r) * s i) * p) := by
      rw [Finset.sum_mul, map_sum]
    _ = τ p := by rw [hfull, one_mul]

theorem traceTransfer_eq_sandwich (I : Finset ι) (r p : A) (s : ι → A) :
    traceTransfer I r p s = r * (∑ i ∈ I, s i * p * star (s i)) * r := by
  simp only [traceTransfer, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem traceTransfer_eq_sum_conjugates (I : Finset ι) (r p : A) (s : ι → A)
    (hr : star r = r) :
    traceTransfer I r p s = ∑ i ∈ I, star (star (s i) * r) * p * (star (s i) * r) := by
  simp only [traceTransfer, star_mul, star_star, hr, mul_assoc]

theorem traceTransfer_nonneg [PartialOrder A] [StarOrderedRing A]
    [IsOrderedAddMonoid A] (I : Finset ι) (r p : A) (s : ι → A)
    (hr : star r = r) (hp : 0 ≤ p) : 0 ≤ traceTransfer I r p s := by
  rw [traceTransfer_eq_sum_conjugates I r p s hr]
  exact Finset.sum_nonneg (fun i _ => star_left_conjugate_nonneg hp _)
end CuntzPureness

end OAI
