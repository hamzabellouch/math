import OAI.MeasureTheory.Falconer.Geometry.ScalarUniformProjection

namespace OAI

/-! The actual equally spaced coefficient set used in the uniform
projection estimate. -/
namespace Falconer

noncomputable def scalarDyadicGrid (n : ℕ) : Finset ℝ :=
  (Finset.range (2^n+1)).image fun i : ℕ => (i : ℝ)/(2:ℝ)^n

theorem scalarDyadicGrid_map_injective (n : ℕ) :
    Function.Injective (fun i : ℕ => (i : ℝ)/(2:ℝ)^n) := by
  intro i j h
  have he := congrArg (fun x : ℝ => x*(2:ℝ)^n) h
  have hpow : (2:ℝ)^n ≠ 0 := by positivity
  simp only [div_mul_cancel₀ _ hpow] at he
  exact Nat.cast_injective he

theorem scalarDyadicGrid_card (n : ℕ) : (scalarDyadicGrid n).card = 2^n+1 := by
  rw [scalarDyadicGrid,Finset.card_image_of_injective _ (scalarDyadicGrid_map_injective n),Finset.card_range]

theorem scalarDyadicGrid_nonempty (n : ℕ) : (scalarDyadicGrid n).Nonempty := by
  apply Finset.card_pos.mp
  rw [scalarDyadicGrid_card]
  exact Nat.zero_lt_succ _

theorem scalarDyadicGrid_bound (n : ℕ) : ∀ c ∈ scalarDyadicGrid n, |c| ≤ 1 := by
  intro c hc
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
  have hiN : i ≤ 2^n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hiR : (i : ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hiN
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))]
  exact (div_le_one (by positivity)).2 hiR

theorem scalarDyadicGrid_separated (n : ℕ) :
    ∀ c ∈ scalarDyadicGrid n, ∀ d ∈ scalarDyadicGrid n, c ≠ d →
      1/(2:ℝ)^n ≤ |c-d| := by
  intro c hc d hd hne
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
  have hij : i ≠ j := by intro he; exact hne (congrArg (fun k : ℕ => (k : ℝ)/(2:ℝ)^n) he)
  have hdist : (1 : ℝ) ≤ |(i : ℝ)-(j : ℝ)| := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hj : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < (2:ℝ)^n)]
  exact div_le_div_of_nonneg_right hdist (by positivity)

theorem scalarDyadicGrid_density (n : ℕ) :
    1 ≤ (1/(2:ℝ)^n)*((scalarDyadicGrid n).card : ℝ) := by
  rw [scalarDyadicGrid_card,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hpow : 0 < (2:ℝ)^n := by positivity
  have hh : (1/(2:ℝ)^n)*((2:ℝ)^n) = 1 := one_div_mul_cancel hpow.ne'
  nlinarith [one_div_pos.mpr hpow]

end Falconer

end OAI
