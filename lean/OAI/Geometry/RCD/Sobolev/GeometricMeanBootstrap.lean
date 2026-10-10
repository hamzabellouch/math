import Mathlib

namespace OAI

/-! # Removing an auxiliary supremum bound by geometric interpolation -/

open Set Filter MeasureTheory
open scoped Topology

namespace RegularPointCoordinates

/-- Iterating an interior estimate with a summable loss removes the
initial upper bound. This is the scalar step from L² to L¹ mean bounds. -/
theorem geometric_mean_bootstrap {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (Ω : Set X) (S : ℕ → Set X) (hS : ∀ i, S i ⊆ Ω)
    {θ b D H B : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hD : 0 ≤ D) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hbalance : θ*b^2 = 1/2)
    (hbound : ∀ᵐ x ∂μ.restrict Ω, u x ≤ B)
    (hstep : ∀ i C, 0 ≤ C →
      (∀ᵐ x ∂μ.restrict (S (i+1)), u x ≤ C) →
      ∀ᵐ x ∂μ.restrict (S i), u x ≤ θ*C+D*(b^2)^i*H) :
    ∀ᵐ x ∂μ.restrict (S 0), u x ≤ 2*D*H := by
  have hiter (n : ℕ) : ∀ i, ∀ᵐ x ∂μ.restrict (S i),
      u x ≤ θ^n*B+2*D*H*(b^2)^i := by
    induction n with
    | zero =>
      intro i
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hS i) hbound] with x hx
      simpa only [pow_zero,one_mul] using hx.trans (le_add_of_nonneg_right (by positivity))
    | succ n hn =>
      intro i
      have hh := hstep i (θ^n*B+2*D*H*(b^2)^(i+1)) (by positivity) (hn (i+1))
      have heq : θ*(θ^n*B+2*D*H*(b^2)^(i+1))+D*(b^2)^i*H =
          θ^(n+1)*B+2*D*H*(b^2)^i := by
        rw [pow_succ,pow_succ]
        have hb : 2*(θ*b^2) = 1 := by linarith only [hbalance]
        calc
          _ = θ^n*θ*B+(2*(θ*b^2)+1)*D*H*(b^2)^i := by ring
          _ = _ := by rw [hb]; ring
      simpa only [heq] using hh
  have hall : ∀ᵐ x ∂μ.restrict (S 0), ∀ n : ℕ, u x ≤ θ^n*B+2*D*H := by
    apply ae_all_iff.mpr
    intro n
    simpa only [pow_zero,mul_one] using hiter n 0
  have hlim : Tendsto (fun n : ℕ => θ^n*B+2*D*H) atTop (𝓝 (2*D*H)) := by
    convert ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const B).add_const (2*D*H) using 1
    simp only [zero_mul,zero_add]
  filter_upwards [hall] with x hx
  exact ge_of_tendsto hlim (Eventually.of_forall hx)

end RegularPointCoordinates

end OAI
