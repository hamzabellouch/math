import Mathlib

namespace OAI

open scoped BigOperators

namespace TriangularLipschitz

lemma radial_telescoping_sum (u : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (u (k+1)-u k)=u m-u 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih]; ring

lemma radial_square_bound (u : ℕ → ℝ) (m : ℕ) {κ g : ℝ} (hκ : 0 ≤ κ)
    (hstep : ∀ k < m, κ*(u (k+1)-u k)^2 ≤ g) :
    κ*(u m-u 0)^2 ≤ (m:ℝ)^2*g := by
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range m)
    (f := fun k => u (k+1)-u k)
  rw [radial_telescoping_sum,Finset.card_range] at hc
  have hs : κ*(∑ k ∈ Finset.range m, (u (k+1)-u k)^2) ≤ (m:ℝ)*g := by
    rw [Finset.mul_sum]
    simpa using Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
  calc
    _ ≤ κ*((m:ℝ)*∑ k ∈ Finset.range m, (u (k+1)-u k)^2) := mul_le_mul_of_nonneg_left hc hκ
    _ = (m:ℝ)*(κ*∑ k ∈ Finset.range m, (u (k+1)-u k)^2) := by ring
    _ ≤ (m:ℝ)*((m:ℝ)*g) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by ring

lemma two_radial_square_bound (u v : ℕ → ℝ) (m : ℕ) {κ g : ℝ} (hκ : 0 ≤ κ)
    (hcenter : u m=v m)
    (hu : ∀ k < m, κ*(u (k+1)-u k)^2 ≤ g)
    (hv : ∀ k < m, κ*(v (k+1)-v k)^2 ≤ g) :
    κ*(u 0-v 0)^2 ≤ 4*(m:ℝ)^2*g := by
  have h₁ := radial_square_bound u m hκ hu
  have h₂ := radial_square_bound v m hκ hv
  have h₃ := mul_nonneg hκ (sq_nonneg ((u m-u 0)+(v m-v 0)))
  rw [hcenter] at h₁ h₃
  nlinarith

end TriangularLipschitz

end OAI
