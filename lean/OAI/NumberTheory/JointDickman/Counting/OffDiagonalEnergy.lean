import OAI.NumberTheory.JointDickman.Counting.BinLabelPositiveEnergy

namespace OAI

/-! # The unequal-coefficient terms of the actual quadratic energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem complex_norm_sq_eq_re_star_mul (z : ℂ) : ‖z‖^2 = (star z * z).re := by
  rw [Complex.sq_norm]
  change Complex.normSq z = ((starRingEnd ℂ) z * z).re
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem norm_sum_sq_eq_double {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ a ∈ s, f a‖^2 = ∑ a ∈ s, ∑ b ∈ s, (star (f a) * f b).re := by
  rw [complex_norm_sq_eq_re_star_mul, star_sum, sum_mul, Complex.re_sum]
  apply sum_congr rfl
  intro a _
  rw [mul_sum, Complex.re_sum]

theorem norm_sum_sq_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ a ∈ s, f a‖^2 = (∑ a ∈ s, ‖f a‖^2) +
      ∑ a ∈ s, ∑ b ∈ s, if a = b then 0 else (star (f a) * f b).re := by
  rw [norm_sum_sq_eq_double, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  rw [complex_norm_sq_eq_re_star_mul]
  have hdiag : (star (f a) * f a).re =
      ∑ b ∈ s, if a = b then (star (f a) * f b).re else 0 := by simp [ha]
  rw [hdiag, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp_all

open Classical in
noncomputable def firstFormOffDiagonal (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2 *
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        if A = D then 0 else
          (star (firstFormAtom B L τ C v J N i.1 i.2 A) *
            firstFormAtom B L τ C v J N i.1 i.2 D).re) / (N : ℝ)

theorem firstFormEnergy_eq_diagonal_add (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) :
    firstFormEnergy B L τ C u v J N = firstFormDiagonal B L τ C u v J N +
      firstFormOffDiagonal B L τ C u v J N := by
  classical
  unfold firstFormEnergy firstFormDiagonal firstFormOffDiagonal
  rw [← add_div, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [← mul_add]
  congr 1
  exact norm_sum_sq_split (auxiliaryPrimes B).powerset
    (firstFormAtom B L τ C v J N i.1 i.2)

/-- Diagonal removal retains half of any positive lower energy constant. -/
theorem positive_offDiagonal_of_energy
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau)
    (C : ℝ) (J : ℕ → ℕ → ℂ) (hJ : ∀ N n, ‖J N n‖ ≤ 2)
    (s : ℕ → ℕ) (hs : StrictMono s) {e : ℝ} (he : 0 < e)
    (henergy : ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight (amplificationMultiplier B)) (J (s N)) (s N) /
          ((B : ℝ)*amplificationMultiplier B)) :
    ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      e/2 ≤ firstFormOffDiagonal B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight (amplificationMultiplier B)) (J (s N)) (s N) /
          ((B : ℝ)*amplificationMultiplier B) := by
  have hd := smooth_diagonal_negligible hFord hM hL hτ hτsmall C J hJ (e/2) (half_pos he)
  filter_upwards [henergy,hd] with B hE hD
  filter_upwards [hE, hs.tendsto_atTop.eventually hD] with N hEN hDN
  rw [firstFormEnergy_eq_diagonal_add, add_div] at hEN
  linarith

end JointDickman

end OAI
