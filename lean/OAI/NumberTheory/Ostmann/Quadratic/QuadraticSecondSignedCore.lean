import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstKernelError
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondError

namespace OAI

/-! # The full signed second Poisson core, at the original first-transform weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

def quadraticPoissonSigns : Finset ℤ := {1, -1, 2, -2}

theorem quadraticPoissonSigns_abs {a : ℤ} (ha : a ∈ quadraticPoissonSigns) :
    1 ≤ |(a : ℝ)| := by
  simp only [quadraticPoissonSigns, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

noncomputable def quadraticSignedSecondCore (ρ : 𝓢(ℝ, ℂ)) (M H J : ℝ)
    (e q K : ℕ) : ℂ :=
  ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
    ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
      quadraticSecondDyadicCore ρ (a : ℤ) (quadraticPoissonSigns_abs a.property) M b H J e q b

theorem quadratic_second_signed_uniform (ρ : 𝓢(ℝ, ℂ))
    (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : quadraticPoissonSigns, ∀ M H J : ℝ,
      0 < M → 0 < H → 1 ≤ J → ∀ e q b : ℕ, 0 < e → q ≠ 1 → 0 < b →
      H ^ 2 ≤ q → (q : ℝ) ≤ 4 * H ^ 2 →
      ‖((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        quadraticSecondDyadicError ρ (a : ℤ) (quadraticPoissonSigns_abs a.property)
          M b H J e q b‖ ≤ C * Real.sqrt M / J ^ A := by
  have hs (a : quadraticPoissonSigns) :=
    quadratic_second_error_normalized ρ (a : ℤ) (quadraticPoissonSigns_abs a.property) hρ A
  choose c hc hbound using hs
  let C := (∑ a : quadraticPoissonSigns, c a) + 1
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun a _ => (hc a).le)) zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro a M H J hM hH hJ e q b he hq hb hqlo hqhi
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hb₁ : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hca : c a ≤ C := by
    have hh := Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ a)
    change c a ≤ (∑ a : quadraticPoissonSigns, c a) + 1
    linarith
  have hd : 1 ≤ Real.sqrt e * Real.sqrt b :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr he₁) (Real.one_le_sqrt.mpr hb₁)
  apply (hbound a M b H J hM hbR hH hJ e q b he hq le_rfl (by linarith) hqlo hqhi).trans
  calc
    _ = (c a * (Real.sqrt M / (Real.sqrt e * Real.sqrt b))) / J ^ A := by ring
    _ ≤ c a * Real.sqrt M / J ^ A := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (div_le_self (Real.sqrt_nonneg _) hd) (hc a).le
    _ ≤ _ := by gcongr

theorem quadratic_signed_second_error (ρ : 𝓢(ℝ, ℂ))
    (hρ : ∀ t < 1 / 2, ρ t = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M H J : ℝ, 0 < M → 0 < H → 1 ≤ J →
      ∀ e q K : ℕ, 0 < e → q ≠ 1 → H ^ 2 ≤ q → (q : ℝ) ≤ 4 * H ^ 2 →
      ‖((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        (quadraticFirstFiniteFrequency ρ M e q K - quadraticSignedSecondCore ρ M H J e q K)‖ ≤
          C * Real.sqrt M * K / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_second_signed_uniform ρ hρ A
  refine ⟨4 * C, by positivity, ?_⟩
  intro M H J hM hH hJ e q K he hq hqlo hqhi
  have hf : quadraticFirstFiniteFrequency ρ M e q K =
      ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
        ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          ∑' c : ℕ+, (1 : DirichletCharacter ℂ q) (c : ZMod q) *
            𝓕 ρ ((a : ℤ) * b * (c : ℝ) ^ 2 / ((e : ℝ) * q / M)) := by
    exact (Finset.sum_coe_sort quadraticPoissonSigns _).symm
  have hid : ((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
      (quadraticFirstFiniteFrequency ρ M e q K - quadraticSignedSecondCore ρ M H J e q K) =
      ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
        ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            quadraticSecondDyadicError ρ (a : ℤ) (quadraticPoissonSigns_abs a.property)
              M b H J e q b) := by
    rw [hf]
    unfold quadraticSignedSecondCore
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b _
    unfold quadraticSecondDyadicError
    ring
  rw [hid]
  have hp (a : quadraticPoissonSigns) (b : ℕ) (hb : b ∈ oddSquarefreeRange K) :
      ‖((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          (((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
            quadraticSecondDyadicError ρ (a : ℤ) (quadraticPoissonSigns_abs a.property)
              M b H J e q b)‖ ≤ C * Real.sqrt M / J ^ A := by
    have hJac (n : ℤ) : ‖(jacobiSym n q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy n q with h | h | h <;> rw [h] <;> norm_num
    have hj : ‖(jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul (hJac _) (hJac _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_mul hj (hc a M H J hM hH hJ e q b he hq
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1 hqlo hqhi)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ ≤ ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K, C * Real.sqrt M / J ^ A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (hp a))
    _ = 4 * ((oddSquarefreeRange K).card : ℝ) * (C * Real.sqrt M / J ^ A) := by
      norm_num [quadraticPoissonSigns]
      ring
    _ ≤ 4 * (K : ℝ) * (C * Real.sqrt M / J ^ A) := by
      gcongr
      exact_mod_cast oddSquarefreeRange_card_le K
    _ = _ := by ring

end Ostmann

end OAI
