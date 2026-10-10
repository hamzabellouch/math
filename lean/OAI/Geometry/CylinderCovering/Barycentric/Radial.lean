import Mathlib

namespace OAI

namespace CylinderCovering.BarycentricRadial

open Set

theorem quotient_strictAntiOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictAntiOn (fun t : ℝ => a / t - b / (1 - t)) (Ioo 0 1) := by
  intro t ht s hs hts
  have hfirst : a / s < a / t := div_lt_div_of_pos_left ha ht.1 hts
  have hsecond : b / (1 - t) < b / (1 - s) :=
    div_lt_div_of_pos_left hb (sub_pos.mpr hs.2) (by linarith)
  linarith

theorem existsUnique_parameter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    ∃! t : ℝ, t ∈ Ioo 0 1 ∧ a / t - b / (1 - t) = z := by
  let f : ℝ → ℝ := fun t => a * (1 - t) - b * t - z * t * (1 - t)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hz : (0 : ℝ) ∈ Icc (f 1) (f 0) := by dsimp [f]; constructor <;> linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn hz
  have ht0 : 0 < t := by
    have hne : t ≠ 0 := by intro H; subst t; simp [f] at hft; linarith
    exact lt_of_le_of_ne ht.1 (Ne.symm hne)
  have ht1 : t < 1 := by
    have hne : t ≠ 1 := by intro H; subst t; simp [f] at hft; linarith
    exact lt_of_le_of_ne ht.2 hne
  have hroot : a / t - b / (1 - t) = z := by
    have htne : t ≠ 0 := ne_of_gt ht0
    have h1ne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    apply (sub_eq_zero.mp)
    apply (mul_eq_zero.mp (show (a / t - b / (1 - t) - z) *
      (t * (1 - t)) = 0 from by
        field_simp
        dsimp [f] at hft
        nlinarith)).resolve_right
    exact mul_ne_zero htne h1ne
  refine ⟨t, ⟨⟨ht0, ht1⟩, hroot⟩, ?_⟩
  intro s hs
  exact (quotient_strictAntiOn ha hb).injOn hs.1 ⟨ht0, ht1⟩ (hs.2.trans hroot.symm)

theorem radial_parameter_positive {a b z t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Ioo 0 1) (hroot : a / t - b / (1 - t) = z) :
    0 < a / t - z * t ∧
    a / t - z * t = b / (1 - t) + z * (1 - t) := by
  have hrad : a / t - z * t = (1 - t) * (a / t) + t * (b / (1 - t)) := by
    rw [← hroot]
    ring
  constructor
  · rw [hrad]
    exact add_pos (mul_pos (sub_pos.mpr ht.2) (div_pos ha ht.1))
      (mul_pos ht.1 (div_pos hb (sub_pos.mpr ht.2)))
  · linarith [hroot]

theorem reconstruction {a b z t : ℝ} (ht : t ∈ Ioo 0 1)
    (hroot : a / t - b / (1 - t) = z) :
    a = (a / t - z * t) * t + z * t ^ 2 ∧
    b = (a / t - z * t) * (1 - t) - z * (1 - t) ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht.1
  have h1ne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  constructor
  · calc
      a = a / t * t := (div_mul_cancel₀ a htne).symm
      _ = _ := by ring
  · have hrad : a / t - z * t = b / (1 - t) + z * (1 - t) := by
      linarith [hroot]
    rw [hrad]
    calc
      b = b / (1 - t) * (1 - t) := (div_mul_cancel₀ b h1ne).symm
      _ = _ := by ring

theorem exists_positive_radial_representation {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    ∃ t S : ℝ, t ∈ Ioo 0 1 ∧ 0 < S ∧
      a = S * t + z * t ^ 2 ∧
      b = S * (1 - t) - z * (1 - t) ^ 2 ∧
      S = a / t - z * t ∧ S = b / (1 - t) + z * (1 - t) := by
  obtain ⟨t, ht, _⟩ := existsUnique_parameter ha hb z
  obtain ⟨hpos, heq⟩ := radial_parameter_positive ha hb ht.1 ht.2
  obtain ⟨hfirst, hsecond⟩ := reconstruction ht.1 ht.2
  exact ⟨t, a / t - z * t, ht.1, hpos, hfirst, hsecond, rfl, heq⟩

theorem velocity_first_difference (t t₀ : ℝ) :
    t ^ 2 - t₀ ^ 2 = 2 * (t - t₀) * t - (t - t₀) ^ 2 := by ring

theorem velocity_second_difference (t t₀ : ℝ) :
    -(1 - t) ^ 2 - (-(1 - t₀) ^ 2) =
      2 * (t - t₀) * (1 - t) + (t - t₀) ^ 2 := by ring

theorem zero_first_representation {b : ℝ} (hb : 0 ≤ b) (z : ℝ) :
    ∃ t S : ℝ, t ∈ Icc 0 1 ∧ 0 ≤ S ∧
      0 = S * t + z * t ^ 2 ∧
      b = S * (1 - t) - z * (1 - t) ^ 2 := by
  by_cases h : 0 ≤ b + z
  · refine ⟨0, b + z, by norm_num, h, by ring, ?_⟩
    ring
  · have hz : z < 0 := by linarith
    have hzne : z ≠ 0 := ne_of_lt hz
    have htlo : 0 ≤ 1 + b / z := by
      have : -1 ≤ b / z := (le_div_iff_of_neg hz).2 (by linarith)
      linarith
    have hthi : 1 + b / z ≤ 1 := by
      have := div_nonpos_of_nonneg_of_nonpos hb (le_of_lt hz)
      linarith
    refine ⟨1 + b / z, -b - z, ⟨htlo, hthi⟩, by linarith, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring

theorem zero_second_representation {a : ℝ} (ha : 0 ≤ a) (z : ℝ) :
    ∃ t S : ℝ, t ∈ Icc 0 1 ∧ 0 ≤ S ∧
      a = S * t + z * t ^ 2 ∧
      0 = S * (1 - t) - z * (1 - t) ^ 2 := by
  obtain ⟨u, S, hu, hS, hzero, haeq⟩ := zero_first_representation ha (-z)
  refine ⟨1 - u, S, ⟨by linarith [hu.2], by linarith [hu.1]⟩, hS, ?_, ?_⟩
  · nlinarith [haeq]
  · nlinarith [hzero]

theorem exists_nonnegative_radial_representation {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ) :
    ∃ t S : ℝ, t ∈ Icc 0 1 ∧ 0 ≤ S ∧
      a = S * t + z * t ^ 2 ∧
      b = S * (1 - t) - z * (1 - t) ^ 2 := by
  rcases eq_or_lt_of_le ha with h | ha'
  · subst a
    exact zero_first_representation hb z
  rcases eq_or_lt_of_le hb with h | hb'
  · subst b
    exact zero_second_representation ha z
  obtain ⟨t, S, ht, hS, hfirst, hsecond, _, _⟩ :=
    exists_positive_radial_representation ha' hb' z
  exact ⟨t, S, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, le_of_lt hS, hfirst, hsecond⟩

end CylinderCovering.BarycentricRadial

end OAI
