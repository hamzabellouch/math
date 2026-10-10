import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import OAI.Analysis.Laughlin.Pair.EnergyReturn

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem normalized_occupation_sum_bound {I : Type*} [Fintype I] (Q : ℕ)
    (c : I → ℝ) (v : I → Space Q) (hc : (∑ i, (c i)^2)=1) :
    occupationNormSq Q (∑ i, (c i : ℂ) • v i) ≤ ∑ i, occupationNormSq Q (v i) := by
  unfold occupationNormSq
  simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm (f := fun i A => ‖(occupationBasis Q).repr (v i) A‖^2)]
  apply Finset.sum_le_sum
  intro A hA
  have ht : ‖∑ i, (c i : ℂ) * (occupationBasis Q).repr (v i) A‖ ≤
      ∑ i, |c i| * ‖(occupationBasis Q).repr (v i) A‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      (norm_sum_le Finset.univ (fun i => (c i : ℂ) * (occupationBasis Q).repr (v i) A))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |c i|)
    (fun i => ‖(occupationBasis Q).repr (v i) A‖)
  simp only [sq_abs,hc,one_mul] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hs

end Laughlin.Fock

end OAI
