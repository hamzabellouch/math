import OAI.NumberTheory.Ostmann.Quadratic.QuadraticArrayMass
import OAI.NumberTheory.Ostmann.Preliminaries.MoebiusSquareRemoval

namespace OAI

/-! # The exact outer-divisor quadratic subseries -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem sum_positive_multiples (P W : ℕ) (hP : 0 < P) (f : ℕ → ℂ) :
    (∑ w ∈ (Finset.Ioc 0 W).filter (fun w => P ∣ w), f w) =
      ∑ n ∈ Finset.Ioc 0 (W / P), f (P * n) := by
  classical
  have hset : (Finset.Ioc 0 W).filter (fun w => P ∣ w) =
      (Finset.Ioc 0 (W / P)).image (fun n => P * n) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw, hPw⟩ := Finset.mem_filter.mp hw
      obtain ⟨hw0, hwW⟩ := Finset.mem_Ioc.mp hw
      have heq : P * (w / P) = w := Nat.mul_div_cancel' hPw
      apply Finset.mem_image.mpr
      refine ⟨w / P, Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hwW⟩, heq⟩
      by_contra hn
      have hz : w / P = 0 := Nat.eq_zero_of_not_pos hn
      simp only [hz, mul_zero] at heq
      omega
    · intro hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hn0, hnW⟩ := Finset.mem_Ioc.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hP hn0, ?_⟩, dvd_mul_right P n⟩
      have hh := (Nat.le_div_iff_mul_le hP).mp hnW
      simpa only [Nat.mul_comm] using hh
  rw [hset, Finset.sum_image]
  intro a _ b _ heq
  exact Nat.eq_of_mul_eq_mul_left hP heq

theorem quadraticDensityTerm_multiple {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ)
    (s P w : ℕ) :
    quadraticDensityTerm g a θ Φ R v s (P * w) =
      quadraticDensityTerm g a θ Φ R v (s * P ^ 2) w := by
  unfold quadraticDensityTerm
  have hg : a * ((P * w : ℕ) : ZMod q) ^ 2 * (s : ZMod q) =
      a * (w : ZMod q) ^ 2 * ((s * P ^ 2 : ℕ) : ZMod q) := by push_cast; ring
  have he : realAdditivePhase (θ * v * ((P * w : ℕ) : ℝ) ^ 2 / q) ^ s =
      realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ (s * P ^ 2) := by
    rw [← realAdditivePhase_nat_mul, ← realAdditivePhase_nat_mul]
    congr 1
    push_cast
    ring
  have hx : (s : ℝ) * v * ((P * w : ℕ) : ℝ) ^ 2 / (R * q) =
      ((s * P ^ 2 : ℕ) : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by push_cast; ring
  rw [hg, he, hx]

noncomputable def positiveQuadraticMultiples {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ)
    (s P : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑' w : ℕ, if 0 < w then quadraticDensityTerm g a θ Φ R v s (P * w) else 0

theorem positiveQuadraticMultiples_eq {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ)
    (s P : ℕ) (hP : 0 < P) (hR : 0 ≤ R) (hv : 0 ≤ v) :
    positiveQuadraticMultiples g a θ Φ R v s P =
      (P : ℂ)⁻¹ * positiveQuadraticSum g a θ Φ R v (s * P ^ 2) := by
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hroot : Real.sqrt (R * q / (((s * P ^ 2 : ℕ) : ℝ) * v)) =
      Real.sqrt (R * q / ((s : ℝ) * v)) / P := by
    have he : R * q / (((s * P ^ 2 : ℕ) : ℝ) * v) =
        (R * q / ((s : ℝ) * v)) / (P : ℝ) ^ 2 := by push_cast; ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq (Nat.cast_nonneg P)]
  unfold positiveQuadraticMultiples positiveQuadraticSum
  simp_rw [quadraticDensityTerm_multiple]
  rw [hroot]
  push_cast
  field_simp

theorem positiveQuadraticMultiples_eq_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ)
    (s P : ℕ) (hP : 0 < P) (hR : 0 < R) (hv : 0 < v) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticMultiples g a θ Φ R v s P =
      ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
        ∑ w ∈ (quadraticCompactCutoff q R v H s).filter (fun w => P ∣ w),
          quadraticDensityTerm g a θ Φ R v s w := by
  classical
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  unfold positiveQuadraticMultiples
  congr 1
  calc
    _ = ∑ n ∈ Finset.Ioc 0 (W / P),
        if 0 < n then quadraticDensityTerm g a θ Φ R v s (P * n) else 0 := by
      apply tsum_eq_sum
      intro n hn
      by_cases hn0 : 0 < n
      · simp only [ite_eq_left hn0]
        by_contra hterm
        have hm := quadraticDensityTerm_mem_cutoff g a θ Φ R v H s s (P * n)
          hR hv hs le_rfl (Nat.mul_pos hP hn0) hΦ hterm
        have hPnW : P * n ≤ W := (Finset.mem_Ioc.mp hm).2
        have hnW : n ≤ W / P := (Nat.le_div_iff_mul_le hP).mpr (by simpa only [Nat.mul_comm] using hPnW)
        exact hn (Finset.mem_Ioc.mpr ⟨hn0, hnW⟩)
      · simp only [ite_eq_right hn0]
    _ = ∑ n ∈ Finset.Ioc 0 (W / P), quadraticDensityTerm g a θ Φ R v s (P * n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact ite_eq_left (Finset.mem_Ioc.mp hn).1
    _ = _ := (sum_positive_multiples P W hP (quadraticDensityTerm g a θ Φ R v s)).symm

end Ostmann

end OAI
