import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlockMean
import OAI.NumberTheory.JointDickman.Arithmetic.BrunGeometric
import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlocks

namespace OAI

/-! # A uniform bound for the product of block means -/
namespace JointDickman
open Finset

 theorem brun_exp_product_bound {ι : Type*} [Fintype ι] (e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) : (∏ i, (1+e i)) ≤ Real.exp (∑ i, e i) := by
  calc
    _ ≤ ∏ i, Real.exp (e i) := prod_le_prod₀ (fun i _ => by linarith [he i])
      (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (e i))
    _ = _ := (Real.exp_sum _ _).symm

 theorem brun_geometric_fin (N : ℕ) : (∑ i : Fin N, 1/(4:ℝ)^(i.val+1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1/(4:ℝ)^(j+1)) N]
  exact brun_geometric_le N

 theorem brun_error_product (N : ℕ) (B : ℝ) :
    (∏ i : Fin N, (1+Real.exp (4*B)/(4:ℝ)^(i.val+1))) ≤ Real.exp (Real.exp (4*B)) := by
  have hs : (∑ i : Fin N, Real.exp (4*B)/(4:ℝ)^(i.val+1)) ≤ Real.exp (4*B) := by
    calc
      _ = Real.exp (4*B)*(∑ i : Fin N, 1/(4:ℝ)^(i.val+1)) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ _ := mul_le_of_le_one_right (Real.exp_pos _).le (brun_geometric_fin N)
  exact (brun_exp_product_bound (fun i : Fin N => Real.exp (4*B)/(4:ℝ)^(i.val+1))
    (fun i => by positivity)).trans (Real.exp_le_exp.mpr hs)

 theorem brun_absence_product_nonneg {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (g : ℕ → ℝ) (hg : ∀ i p, p ∈ P i → g p ≤ 1) :
    0 ≤ ∏ i, ∏ p ∈ P i, (1-g p) := by
  apply prod_nonneg
  intro i _
  exact prod_nonneg (fun p hp => sub_nonneg.mpr (hg i p hp))

 theorem brunBlockMean_product_bound {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (g : ℕ → ℝ) (r : ι → ℕ) {B : ℝ}
    (hg : ∀ i p, p ∈ P i → 0 ≤ g p ∧ g p < 1)
    (hB : ∀ i, (∏ p ∈ P i, (1-g p)⁻¹) ≤ Real.exp B) :
    (∏ i, brunMean (P i) g (r i)) ≤
      (∏ i, ∏ p ∈ P i, (1-g p)) * ∏ i, (1+Real.exp (4*B)/(4:ℝ)^(r i)) := by
  rw [← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _
    exact brunMean_nonneg (P i) g (r i) (fun p hp => ⟨(hg i p hp).1,(hg i p hp).2.le⟩)
  · intro i _
    exact brunMean_relative (P i) g (r i) (hg i) (hB i)

 theorem brunBlockMean_product (N : ℕ) (P : Fin N → Finset ℕ) (g : ℕ → ℝ) {B : ℝ}
    (hg : ∀ i p, p ∈ P i → 0 ≤ g p ∧ g p < 1)
    (hB : ∀ i, (∏ p ∈ P i, (1-g p)⁻¹) ≤ Real.exp B) :
    (∏ i, brunMean (P i) g (i.val+1)) ≤
      (∏ i, ∏ p ∈ P i, (1-g p))*Real.exp (Real.exp (4*B)) := by
  exact (brunBlockMean_product_bound P g (fun i => i.val+1) hg hB).trans
    (mul_le_mul_of_nonneg_left (brun_error_product N B)
      (brun_absence_product_nonneg P g (fun i p hp => (hg i p hp).2.le)))

end JointDickman

end OAI
