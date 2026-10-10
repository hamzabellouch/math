import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelPoisson
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondCutoffs

namespace OAI

/-! # Common cutoffs for the original small-squarefree-kernel block -/

namespace Ostmann

open scoped SchwartzMap BigOperators

noncomputable def quadraticSmallScale (M : ℝ) (b : ℕ) : ℝ := Real.sqrt (M / b)

theorem quadraticSmallScale_pos {M : ℝ} {b : ℕ} (hM : 0 < M) (hb : 0 < b) :
    0 < quadraticSmallScale M b := by unfold quadraticSmallScale; positivity

theorem quadraticSmallScale_argument {M : ℝ} {b : ℕ}
    (hM : 0 < M) (hb : 0 < b) (x : ℝ) :
    (x / quadraticSmallScale M b) ^ 2 = x ^ 2 * b / M := by
  rw [div_pow, quadraticSmallScale, Real.sq_sqrt (by positivity)]
  field_simp

theorem quadraticSmallScale_dyadic {M B : ℝ} {b : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hb : B ≤ b) (hb' : (b : ℝ) ≤ 2 * B) :
    Real.sqrt (M / B) / 2 ≤ quadraticSmallScale M b ∧
      quadraticSmallScale M b ≤ 2 * Real.sqrt (M / B) := by
  have hb₀ : 0 < (b : ℝ) := hB.trans_le hb
  have hlo : M / B ≤ 2 * (M / b) := by
    calc
      _ = 2 * (M / (2 * B)) := by ring
      _ ≤ _ := by gcongr
  have hhi : M / b ≤ M / B := div_le_div_of_nonneg_left hM.le hB hb
  have hs₀ := Real.sq_sqrt (div_nonneg hM.le hB.le)
  have hs := Real.sq_sqrt (div_nonneg hM.le hb₀.le)
  have hn₀ := Real.sqrt_nonneg (M / B)
  have hn := Real.sqrt_nonneg (M / b)
  unfold quadraticSmallScale
  constructor <;> nlinarith

noncomputable def quadraticSmallDyadicCore (ρ : 𝓢(ℝ, ℂ))
    (M B J : ℝ) (q b : ℕ) : ℂ :=
  quadraticSmallPoissonCore q ρ (quadraticSmallScale M b)
    (quadraticSecondLower (Real.sqrt (M / B)) J)
    (quadraticSecondUpper (Real.sqrt (M / B)) J) (quadraticSecondWindow J)

theorem quadratic_small_dyadic (ρ : 𝓢(ℝ, ℂ)) (hρ : ρ 0 = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M B J : ℝ), 0 < M → 0 < B → 1 ≤ J →
      ∀ (q b : ℕ), [NeZero q] → q ≠ 1 → B ≤ b → (b : ℝ) ≤ 2 * B →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ρ ((n : ℝ) ^ 2 * b / M)) - quadraticSmallDyadicCore ρ M B J q b‖ ≤
          C * quadraticSmallScale M b / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_small_kernel_poisson ρ hρ A
  refine ⟨C, hC, ?_⟩
  intro M B J hM hB hJ q b _ hq hb hb'
  have hb₀ : 0 < b := by exact_mod_cast (hB.trans_le hb)
  obtain ⟨hlo, hhi⟩ := quadraticSmallScale_dyadic hM hB hb hb'
  obtain ⟨hU, hV, hUX, hXV, hL⟩ := quadratic_second_cutoffs
    (show 0 < Real.sqrt (M / B) by positivity) hJ hlo hhi
  simpa only [quadraticSmallScale_argument hM hb₀, quadraticSmallDyadicCore] using
    hc q hq (quadraticSmallScale M b)
      (quadraticSecondLower (Real.sqrt (M / B)) J)
      (quadraticSecondUpper (Real.sqrt (M / B)) J) J
      (quadraticSmallScale_pos hM hb₀) hU hV hJ hUX hXV (quadraticSecondWindow J) hL

end Ostmann

end OAI
