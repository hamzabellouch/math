import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicCubic

namespace OAI

/-! The convergent quadratic-logarithmic dyadic tail used for two prime forms. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_reciprocal_square_tail (K L : ℕ) (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc K L,((k:ℝ)^2)⁻¹) ≤ 2/(K:ℝ) := by
  have hsets : Finset.Icc K L=Finset.Ioo (K-1) (L+1) := by ext k; simp; omega
  rw [hsets]
  have hh := sum_Ioo_inv_sq_le (α:=ℝ) (K-1) (L+1)
  have he : ((K-1:ℕ):ℝ)+1=K := by exact_mod_cast (show K-1+1=K by omega)
  rwa [he] at hh

lemma finite_dyadic_quadratic_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) (K L : ℕ) (hK : 1 ≤ K) {A : ℝ} (hA : 0 ≤ A)
    (hn : ∀ a ∈ Q,n a ∈ Finset.Icc K L)
    (hlo : ∀ a ∈ Q,(2:ℝ)^(n a)/4 ≤ v a)
    (hcount : ∀ k ∈ Finset.Icc K L,((Q.filter (fun a => n a=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^2) :
    (∑ a ∈ Q,(v a)⁻¹) ≤ 8*A/(K:ℝ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (k : ℕ) (hk : k ∈ Finset.Icc K L) :
      (∑ a ∈ Q.filter (fun a => n a=k),(v a)⁻¹) ≤ 4*A*((k:ℝ)^2)⁻¹ := by
    have hy : (0:ℝ) < (2:ℝ)^k := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => n a=k),4/(2:ℝ)^k := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
        have hh := hlo a ha
        rw [he] at hh
        simpa only [inv_div] using inv_anti₀ (div_pos hy (by norm_num)) hh
      _ = ((Q.filter (fun a => n a=k)).card:ℝ)*(4/(2:ℝ)^k) := by simp
      _ ≤ (A*(2:ℝ)^k/(k:ℝ)^2)*(4/(2:ℝ)^k) :=
        mul_le_mul_of_nonneg_right (hcount k hk) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc K L,4*A*((k:ℝ)^2)⁻¹ := Finset.sum_le_sum hf
    _ = 4*A*(∑ k ∈ Finset.Icc K L,((k:ℝ)^2)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ 4*A*(2/(K:ℝ)) := mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail K L hK) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
