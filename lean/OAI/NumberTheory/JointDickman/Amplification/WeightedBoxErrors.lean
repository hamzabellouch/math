import OAI.NumberTheory.JointDickman.Amplification.GeometricBoxErrors

namespace OAI

/-! # Uniform geometric error bounds with bounded scalar box weights -/

namespace JointDickman
open Finset

theorem geometric_weighted_box_error_sum {B : ℕ} (hB : 1 ≤ B) {t : ℝ} (ht : 0 < t)
    (S : Finset ℤ)
    (hS : ∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B))
    (E r : ℤ → ℂ) {T C R p : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hr : ∀ k ∈ S, ‖r k‖ ≤ R) (hE : ∀ k ∈ S, T*‖E k‖ ≤ C*(B : ℝ)^p) :
    T*‖∑ k ∈ S, r k*E k‖ ≤ ((8/(5*t)+1)*(R*C))*(B : ℝ)^(p+1) := by
  apply geometric_box_error_sum hB ht S hS (fun k => r k*E k) hT (mul_nonneg hR hC)
  intro k hk
  rw [norm_mul]
  calc
    _ = ‖r k‖*(T*‖E k‖) := by ring
    _ ≤ R*(C*(B : ℝ)^p) := mul_le_mul (hr k hk) (hE k hk) (by positivity) hR
    _ = _ := by ring

end JointDickman

end OAI
