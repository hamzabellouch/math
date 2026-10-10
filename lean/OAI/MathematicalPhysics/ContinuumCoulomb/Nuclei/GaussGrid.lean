import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussPhysicalCell

namespace OAI

/-! Error accounting for a finite rectangular selection of equal-mass Gauss
cells. The constants may vary between cells, retaining spatial decay. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem interval_grid_integral {N : ℕ} (a h : ℝ) (f : ℝ → ℝ)
    (hf : ∀ k < N, IntervalIntegrable f volume (a+k*h) (a+(k+1)*h)) :
    (∫ x : ℝ in a..(a+N*h), f x) =
      ∑ k ∈ Finset.range N, ∫ x : ℝ in (a+k*h)..(a+(k+1)*h), f x := by
  simpa only [Nat.cast_zero,zero_mul,add_zero,Nat.cast_add,Nat.cast_one] using
    (intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => a+k*h)
      (fun k hk => by simpa only [Nat.cast_add,Nat.cast_one] using hf k hk)).symm

/-- The fourth-order total estimate retains the sum of volume-weighted local
fourth derivative bounds, rather than multiplying by the entire box volume. -/
theorem weighted_cubature_error {ι : Type*} [Fintype ι] (h rho : ℝ)
    (Q I C : ι → ℝ) (hrho : 0 ≤ rho)
    (herr : ∀ i, |Q i-I i| ≤ C i*h^7) :
    |rho*(∑ i, Q i)-rho*(∑ i, I i)| ≤ rho*h^4*(∑ i, C i*h^3) := by
  rw [← mul_sub,abs_mul,abs_of_nonneg hrho,← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hrho).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => herr i)) hrho).trans_eq
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ContinuumCoulomb

end

end OAI
