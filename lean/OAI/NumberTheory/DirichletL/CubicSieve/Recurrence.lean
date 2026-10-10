import OAI.NumberTheory.DirichletL.CubicSieve.Smoothed
import OAI.NumberTheory.DirichletL.CubicSieve.Majorant
import OAI.NumberTheory.DirichletL.CubicSieve.ZeroMode

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_smoothed_frequency_recurrence (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (_hunit : ∀ j, cols j ≠ 1) (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols hunit a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hf0 : f 0 = 0 := cubicDualRow_zero cols (fun j => (hcols j).1) hunit a W M
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads f hf hf0]
  exact mul_le_mul_of_nonneg_left hb hM.le

theorem cubic_smoothed_frequency_recurrence_all (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (((2 / N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ + C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads_with_zero f hf]
  apply mul_le_mul_of_nonneg_left _ hM.le
  exact (norm_add_le _ _).trans (add_le_add
    (cubicDualRow_zero_bound cols (fun j => (hcols j).1) hc a W M N hN0
      (fun j => (hcols j).2.1)) hb)

end
end SevenEighths.CubicSieve

end OAI
