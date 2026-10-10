import Mathlib

namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped ENNReal Pointwise

namespace StrictFilling

theorem contact_volume_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (K : Set E) (hK : Convex ℝ K) (φ : E →ᵃ[ℝ] ℝ)
    (hbound : ∀ x ∈ K, |φ x| ≤ 1)
    (g : E) (hg : g ∈ K) (hstrict : |φ g| ≤ 1 / 2)
    (hfinite : μ K ≠ ⊤) (hpositive : μ K ≠ 0)
    (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    (μ (K ∩ {x | 1 - s < |φ x|})).toReal / (μ K).toReal ≤
      1 - (1 - 2 * s) ^ Module.finrank ℝ E := by
  let r : ℝ := 1 - 2 * s
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr' : 0 ≤ 1 - r := by dsimp [r]; linarith
  let H : Set E := K ∩ {x | |φ x| ≤ 1 - s}
  have hsub : H ⊆ K := Set.inter_subset_left
  have himage : AffineMap.homothety g r '' K ⊆ H := by
    rintro y ⟨x, hx, rfl⟩
    have heq : AffineMap.homothety g r x = (1 - r) • g + r • x := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
      abel
    have hφ : φ (AffineMap.homothety g r x) = r * φ x + (1 - r) * φ g := by
      rw [AffineMap.homothety_apply, φ.map_vadd, map_smul, φ.linearMap_vsub]
      simp only [smul_eq_mul, vsub_eq_sub, vadd_eq_add]
      ring
    constructor
    · rw [heq]
      exact hK hg hx hr' hr (by ring)
    · change |φ (AffineMap.homothety g r x)| ≤ 1 - s
      rw [hφ]
      calc
        |r * φ x + (1 - r) * φ g| ≤ |r * φ x| + |(1 - r) * φ g| := abs_add_le _ _
        _ = r * |φ x| + (1 - r) * |φ g| := by rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hr']
        _ ≤ r * 1 + (1 - r) * (1 / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left (hbound x hx) hr)
            (mul_le_mul_of_nonneg_left hstrict hr')
        _ = 1 - s := by dsimp [r]; ring
  have hHmeas : NullMeasurableSet H μ :=
    (hK.nullMeasurableSet μ).inter
      (isClosed_le φ.continuous_of_finiteDimensional.abs continuous_const).measurableSet.nullMeasurableSet
  have hHfinite : μ H ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono hsub)
  have hmass : ENNReal.ofReal (r ^ Module.finrank ℝ E) * μ K ≤ μ H := by
    have hm := measure_mono himage (μ := μ)
    rwa [addHaar_image_homothety, abs_of_nonneg (pow_nonneg hr _)] at hm
  have hmassR : r ^ Module.finrank ℝ E * (μ K).toReal ≤ (μ H).toReal := by
    have hh := ENNReal.toReal_mono hHfinite hmass
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)] using hh
  have hbad : K ∩ {x | 1 - s < |φ x|} = K \ H := by
    ext x
    simp only [H, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨hx, hl⟩
      exact ⟨hx, fun hh => (not_le_of_gt hl) hh.2⟩
    · rintro ⟨hx, hn⟩
      exact ⟨hx, lt_of_not_ge (fun hh => hn ⟨hx, hh⟩)⟩
  rw [hbad, measure_sdiff hsub hHmeas hHfinite,
    ENNReal.toReal_sub_of_le (measure_mono hsub) hfinite]
  apply (div_le_iff₀ (ENNReal.toReal_pos hpositive hfinite)).2
  dsimp [r] at hmassR
  nlinarith

lemma contraction_volume_bound (m : ℕ) (s : ℝ) (_hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    1 - (1 - 2 * s) ^ m ≤ 2 * (m : ℝ) * s := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -2 * s by linarith) m
  have heq : 1 + -2 * s = 1 - 2 * s := by ring
  rw [heq] at h
  nlinarith

end StrictFilling

end

end OAI
