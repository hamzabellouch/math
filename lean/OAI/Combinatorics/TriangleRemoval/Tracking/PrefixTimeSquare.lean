import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedTemplateEncoding
import OAI.Combinatorics.TriangleRemoval.Tracking.PolynomialExponentialPrefixEnvelope

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefixTime_le_square (n : ℕ) : prefixTime n ≤ n^2 := by
  have hf : prefixTargetTime n ≤ (n : ℝ)^2 := by
    unfold prefixTargetTime
    have h₁ : 0 ≤ 1/(n : ℝ) := by positivity
    have h₂ : 0 ≤ prefixTargetDensity n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h₃ := sq_nonneg (n : ℝ)
    nlinarith
  calc
    prefixTime n ≤ ⌊(n : ℝ)^2⌋₊ := Nat.floor_le_floor hf
    _ = n^2 := by simp only [← Nat.cast_pow,Nat.floor_natCast]

theorem rooted_noise_chances_le (H n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (RootedCountIndex H n)*2*(prefixTime n+1) ≤
      rootedFamilySize H * 2^(H+2)*n^(H+2) := by
  have hpow : (n+1)^H ≤ (2*n)^H := Nat.pow_le_pow_left (by omega) H
  have hn2 : 1 ≤ n^2 := one_le_pow₀ hn
  have ht : prefixTime n+1 ≤ 2*n^2 := by
    have hh := prefixTime_le_square n
    omega
  calc
    _ ≤ (rootedFamilySize H*(n+1)^H)*2*(2*n^2) := by
      gcongr
      exact rootedCountIndex_card_le H n
    _ ≤ (rootedFamilySize H*(2*n)^H)*2*(2*n^2) := by gcongr
    _ = _ := by rw [mul_pow,pow_add,pow_add]; ring

theorem rooted_noise_budget_envelope (H : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (RootedCountIndex H n) : ℝ)*2*(prefixTime n+1)*
        Real.exp (-(n : ℝ)^κ) ≤ Real.exp (-(Real.log n)^(4/3 : ℝ)) := by
  filter_upwards [polynomial_exponential_le_prefix_envelope
    ((rootedFamilySize H : ℝ)*2^(H+2)) (H+2) κ hκ,
    eventually_ge_atTop (1 : ℕ)] with n hb hn
  apply le_trans _ hb
  have hh : (Fintype.card (RootedCountIndex H n) : ℝ)*2*(prefixTime n+1) ≤
      (rootedFamilySize H : ℝ)*2^(H+2)*(n : ℝ)^(H+2) := by
    exact_mod_cast rooted_noise_chances_le H n hn
  have he : (n : ℝ)^((H : ℝ)+2) = (n : ℝ)^(H+2 : ℕ) := by
    rw [← Real.rpow_natCast]
    norm_cast
  rw [he]
  exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end SharpTerminalLeave

end

end OAI
