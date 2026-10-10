import OAI.MeasureTheory.Falconer.Estimates.RegularizationSelection
import OAI.MeasureTheory.Falconer.Estimates.RegularizationQuantifiers

namespace OAI

/-! # Polynomial class count and discarded mass in every dimension -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularization_count_polynomial (Q : DyadicCube d) (μ : Measure (Space d))
    {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N) (t : ℝ≥0∞) :
    (regularizationIndex Q μ N (N/H) t).card ≤ N^(4*H+2) := by
  have hN : 1 ≤ N := by omega
  have h₁ : d*N+1 ≤ N^2 := by nlinarith
  have h₂ : (d+2)*N+1 ≤ N^2 := by nlinarith
  have hb := (PlanarFalconer.division_blocks_control hH hNH).2
  calc
    _ ≤ (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) := regularizationIndex_card Q μ N (N/H) t
    _ ≤ (N^2)^(2*H)*N^2 := Nat.mul_le_mul
      ((Nat.pow_le_pow_left h₁ _).trans (Nat.pow_le_pow_right (by positivity) hb)) h₂
    _ = N^(4*H+2) := by rw [← pow_mul,← pow_add]; congr 1; omega

theorem block_polynomial_exponent {H : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hlam₁ : lam ≤ 1) (hH : (H:ℝ) ≤ 1/lam+2) :
    ((4*H+2:ℕ):ℝ) ≤ 14/lam := by
  have hm := mul_le_mul_of_nonneg_right hH hlam.le
  have hi : (1/lam+2)*lam = 1+2*lam := by field_simp
  rw [hi] at hm
  apply (le_div_iff₀ hlam).mpr
  push_cast
  nlinarith

theorem regularization_discarded_global (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (hcarry : μ Q.carrierᶜ = 0)
    {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N) (t : ℝ≥0∞) :
    μ (⋃ T ∈ regularizationIndex Q μ N (N/H) t, regularizationSet Q μ N (N/H) T)ᶜ ≤
      ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t := by
  let U := ⋃ T ∈ regularizationIndex Q μ N (N/H) t, regularizationSet Q μ N (N/H) T
  have hsub : Uᶜ ⊆ (Q.carrier \ U) ∪ Q.carrierᶜ := by
    intro x hx
    by_cases h : x ∈ Q.carrier
    · exact Or.inl ⟨h,hx⟩
    · exact Or.inr h
  have hc : (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) ≤ N^(4*H+2) := by
    have hN : 1 ≤ N := by omega
    have h₁ : d*N+1 ≤ N^2 := by nlinarith
    have h₂ : (d+2)*N+1 ≤ N^2 := by nlinarith
    have hb := (PlanarFalconer.division_blocks_control hH hNH).2
    calc
      _ ≤ (N^2)^(2*H)*N^2 := Nat.mul_le_mul
        ((Nat.pow_le_pow_left h₁ _).trans (Nat.pow_le_pow_right (by positivity) hb)) h₂
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  calc
    _ ≤ μ (Q.carrier \ U) + μ Q.carrierᶜ := (measure_mono hsub).trans (measure_union_le _ _)
    _ = μ (Q.carrier \ U) := by rw [hcarry,add_zero]
    _ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + ((d*N+1)^(N/(N/H)+1)*((d+2)*N+1):ℕ)*t :=
      regularization_discarded_mass Q hQ μ N (N/H) t
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' (by exact_mod_cast hc) le_rfl)

end Falconer.Regularization

end OAI
