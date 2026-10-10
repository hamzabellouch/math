import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_weighted_cover (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K := by
  have hp (v : α) : x v^K≤∑ i∈T,if a i≤x v then (2*a i)^K else 0 := by
    by_cases hv : 0<x v
    · obtain ⟨i,hi,hix,hxi⟩:=hcover v hv
      apply (pow_le_pow_left₀ (hx v) hxi K).trans
      have hs:=Finset.single_le_sum (f := fun j => if a j≤x v then (2*a j)^K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa only [ite_eq_left hix] using hs
    · have hz : x v=0 := le_antisymm (le_of_not_gt hv) (hx v)
      rw [hz,zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hp v)).trans_eq
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ v,if a i≤x v then (2*a i)^K else 0)=
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*(2*a i)^K := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he,mul_pow]
  ring

theorem moment_quadratic_tail (x : α → ℝ) (a C : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : 2≤K) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^2≤C i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,C i*a i^(K-2) := by
  apply (moment_weighted_cover x a T K (by omega) hx ha hcover).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  have he : K=2+(K-2) := by omega
  calc
    _ = (((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^2)*a i^(K-2) := by
      have hp : a i^K=a i^2*a i^(K-2) := by rw [←pow_add,←he]
      rw [hp]
      ring
    _ ≤ C i*a i^(K-2) := mul_le_mul_of_nonneg_right (hcount i hi) (pow_nonneg (ha i hi) _)

end SharpRamseyFive.DyadicMoments

end OAI
