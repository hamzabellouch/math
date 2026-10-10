import OAI.Geometry.HeilbronnTriangle.ZeroNormalDyadic

namespace OAI


noncomputable section
namespace Problem355.ZeroCountNormalization

open Matrix
open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

theorem log_four_mul_le_two_log_two_mul {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) ≤ 2 * Real.log (2 * N) := by
  have hpos : 0 < 4 * N := by positivity
  have hscale : 4 * N ≤ (2 * N) ^ 2 := by nlinarith
  have h := Real.log_le_log hpos hscale
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem normal_log_le_squared_log {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) / Real.log 2 ≤
      (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlower : Real.log (2 : ℝ) ≤ Real.log (2 * N) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hratio : 1 ≤ Real.log (2 * N) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa using hlower)
  calc
    Real.log (4 * N) / Real.log 2 ≤
        (2 * Real.log (2 * N)) / Real.log 2 :=
      div_le_div_of_nonneg_right (log_four_mul_le_two_log_two_mul hN) hlog2.le
    _ = 2 * (Real.log (2 * N) / Real.log 2) := by ring
    _ ≤ 2 * (Real.log (2 * N) / Real.log 2) ^ 2 := by nlinarith
    _ = (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 := by ring

theorem count_le_squared_log_of_one_log {mass C N I : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C)
    (hcount : mass ≤ 4 * (C * N ^ 6 / I ^ 2) *
      (Real.log (4 * N) / Real.log 2)) :
    mass ≤ (8 * C / (Real.log 2) ^ 2) *
      (Real.log (2 * N)) ^ 2 * N ^ 6 / I ^ 2 := by
  calc
    mass ≤ 4 * (C * N ^ 6 / I ^ 2) *
        (Real.log (4 * N) / Real.log 2) := hcount
    _ ≤ 4 * (C * N ^ 6 / I ^ 2) *
        ((2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2) :=
      mul_le_mul_of_nonneg_left (normal_log_le_squared_log hN) (by positivity)
    _ = _ := by ring

theorem weighted_count_le_squared_log_of_normal_shell_bound
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (N : ℕ) (hN : 1 ≤ N)
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ 2 * (N : ℤ))
    (C I : ℝ) (hC : 0 ≤ C)
    (hshell : ∀ i : ℕ,
      ∑ w ∈ (PrimitiveNormal.normalBox (2 * (N : ℤ))).filter (fun w =>
        (2 : ℝ) ^ i ≤ ‖PrimitiveNormal.toEuclidean w‖ ∧
          ‖PrimitiveNormal.toEuclidean w‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ C * (N : ℝ) ^ 6 / I ^ 2) :
    ∑ A ∈ S, W A ≤ (8 * C / (Real.log 2) ^ 2) *
      (Real.log (2 * (N : ℝ))) ^ 2 * (N : ℝ) ^ 6 / I ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply count_le_squared_log_of_one_log hNR hC
  have hX : (1 : ℤ) ≤ 2 * (N : ℤ) := by omega
  have h := PrimitiveNormal.weighted_count_le_log_of_normal_shell_bound S W hW
    hdet hheight hproj (2 * (N : ℤ)) hX hbound
    (show 0 ≤ C * (N : ℝ) ^ 6 / I ^ 2 by positivity) hshell
  have harg : (2 : ℝ) * ((2 * (N : ℤ) : ℤ) : ℝ) = 4 * (N : ℝ) := by
    push_cast
    ring
  rw [harg] at h
  exact h

theorem normalization_constant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ 8 * C / (Real.log 2) ^ 2 := by positivity

theorem normalization_constant_pos {C : ℝ} (hC : 0 < C) :
    0 < 8 * C / (Real.log 2) ^ 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

end Problem355.ZeroCountNormalization

end

end OAI
