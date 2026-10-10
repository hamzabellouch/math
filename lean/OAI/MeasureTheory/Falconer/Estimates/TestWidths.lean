import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # The width and buffer scales of the all-dimensional tests

These are the exponents 500 and 50 in the all-dimensional test family.
-/

namespace Falconer

noncomputable def angularTestWidth (N : ℕ) (σ : ℝ) (J i n : ℕ) : ℝ :=
  (2-(i:ℝ)/(J:ℝ))/(2:ℝ)^n*((2:ℝ)^N)^(500*σ)

noncomputable def angularTestRadius (N : ℕ) (σ : ℝ) (l : ℕ) : ℝ :=
  min 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*σ))

theorem angularTestRadius_pos (N : ℕ) (σ : ℝ) (l : ℕ) :
    0 < angularTestRadius N σ l := by unfold angularTestRadius; positivity

theorem angularTestWidth_zero (N : ℕ) (σ : ℝ) (J n : ℕ) :
    angularTestWidth N σ J 0 n = 2/(2:ℝ)^n*((2:ℝ)^N)^(500*σ) := by
  simp [angularTestWidth]

theorem angularTestWidth_gap (N : ℕ) (σ : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    angularTestWidth N σ J i n-angularTestWidth N σ J (i+1) n =
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJ.ne'
  simp only [angularTestWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem angularTestWidth_lower (N : ℕ) (σ : ℝ) {J i : ℕ}
    (hJ : 0 < J) (hi : i ≤ J) (n : ℕ) :
    ((2:ℝ)^N)^(500*σ)/(2:ℝ)^n ≤ angularTestWidth N σ J i n := by
  have hj : 0 < (J:ℝ) := Nat.cast_pos.mpr hJ
  have hi' : (i:ℝ) ≤ J := Nat.cast_le.mpr hi
  have hcoeff : 1 ≤ 2-(i:ℝ)/(J:ℝ) := by
    have := (div_le_one hj).mpr hi'
    linarith
  unfold angularTestWidth
  calc
    _ = (1/(2:ℝ)^n)*((2:ℝ)^N)^(500*σ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff (by positivity)) (by positivity)

theorem uniform_angularTestWidth_gap {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      angularTestWidth N σ J (i+1) n+
        (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      angularTestWidth N σ J i n := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 450*σ) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := Nat.cast_pos.mpr hJ
  have hR : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*σ))
  have he : ((2:ℝ)^N)^(450*σ)*((2:ℝ)^N)^(50*σ) =
      ((2:ℝ)^N)^(500*σ) := by rw [← Real.rpow_add hR]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by
    rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*σ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*σ))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← angularTestWidth_gap N σ hJ i n] at hb
  linarith

theorem dyadic_suffix_error {a p t : ℕ} (h : a+t ≤ 2*p) :
    (1/(2:ℝ)^p)^2/(1/(2:ℝ)^a) ≤ 1/(2:ℝ)^t := by
  have he : (1/(2:ℝ)^p)^2/(1/(2:ℝ)^a) = (2:ℝ)^a/((2:ℝ)^p)^2 := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
  simpa only [pow_add,pow_mul,one_mul,mul_comm 2 p] using hp

theorem uniform_suffix_test_width {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (C K : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p t : ℕ, a+t ≤ 2*p → ∀ i ≤ J,
      C/(2:ℝ)^t+K*((1/(2:ℝ)^p)^2/(1/(2:ℝ)^a)) ≤
        angularTestWidth N σ J i t := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 500*σ) (C+K)
  refine ⟨N₀,?_⟩
  intro N hN a p t hapt i hi
  calc
    _ ≤ C/(2:ℝ)^t+K*(1/(2:ℝ)^t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (dyadic_suffix_error hapt) hK)
    _ = (C+K)/(2:ℝ)^t := by ring
    _ ≤ ((2:ℝ)^N)^(500*σ)/(2:ℝ)^t :=
      div_le_div_of_nonneg_right (hN₀ N hN) (by positivity)
    _ ≤ _ := angularTestWidth_lower N σ hJ hi t

end Falconer

end OAI
