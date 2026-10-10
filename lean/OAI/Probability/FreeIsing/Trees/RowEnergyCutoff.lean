import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Problem367.RowEnergyCutoff

theorem lintegral_tsum_sq_sub_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) {X Y : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i)) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((X i ω - Y i ω) ^ 2) ∂P) ≤
      2 * (∫⁻ ω, ∑' i, ENNReal.ofReal (X i ω ^ 2) ∂P) +
      2 * (∫⁻ ω, ∑' i, ENNReal.ofReal (Y i ω ^ 2) ∂P) := by
  have hmX : Measurable (fun ω => ∑' i, ENNReal.ofReal (X i ω ^ 2)) :=
    Measurable.tsum fun i => ((hX i).pow_const 2).ennreal_ofReal
  have hmY : Measurable (fun ω => ∑' i, ENNReal.ofReal (Y i ω ^ 2)) :=
    Measurable.tsum fun i => ((hY i).pow_const 2).ennreal_ofReal
  calc
    _ ≤ ∫⁻ ω, 2 * (∑' i, ENNReal.ofReal (X i ω ^ 2)) +
        2 * (∑' i, ENNReal.ofReal (Y i ω ^ 2)) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro i
      have h : (X i ω - Y i ω) ^ 2 ≤ 2 * X i ω ^ 2 + 2 * Y i ω ^ 2 := by
        nlinarith [sq_nonneg (X i ω + Y i ω)]
      calc
        _ ≤ ENNReal.ofReal (2 * X i ω ^ 2 + 2 * Y i ω ^ 2) :=
          ENNReal.ofReal_le_ofReal h
        _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun ω =>
          (2 : ℝ≥0∞) * (∑' i, ENNReal.ofReal (X i ω ^ 2))) from
          measurable_const.mul hmX),
        lintegral_const_mul _ hmX, lintegral_const_mul _ hmY]

theorem lintegral_Ioc_prod_le_add
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {f : ℝ × Ω → ℝ≥0∞} (hf : Measurable f) (δ T : ℝ) :
    (∫⁻ q, f q ∂(volume.restrict (Ioc 0 T)).prod P) ≤
      (∫⁻ q, f q ∂(volume.restrict (Ioc 0 δ)).prod P) +
      (∫⁻ q, f q ∂(volume.restrict (Ioc δ T)).prod P) := by
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hf.aemeasurable,
    lintegral_prod _ hf.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioc 0 δ ∪ Ioc δ T, ∫⁻ ω, f (t, ω) ∂P := by
      apply lintegral_mono_set
      intro t ht
      by_cases h : t ≤ δ
      · exact Or.inl ⟨ht.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, ht.2⟩
    _ ≤ _ := lintegral_union_le _ _ _

theorem tendsto_zero_of_cutoff
    {E : ℕ → ℝ≥0∞} {L : ℝ → ℕ → ℝ≥0∞} {K : ℝ → ℝ≥0∞}
    (hK : Tendsto K (𝓝 0) (𝓝 0))
    (hsplit : ∀ δ, 0 < δ → δ ≤ 1 → ∀ n, E n ≤ K δ + L δ n)
    (hL : ∀ δ, 0 < δ → Tendsto (L δ) atTop (𝓝 0)) :
    Tendsto E atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), K δ ≤ ε / 2 :=
    (ENNReal.tendsto_nhds_zero.mp hK _ hhalf).filter_mono inf_le_left
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hone : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono
      (fun _ h => h.le)).filter_mono inf_le_left
  obtain ⟨δ, hδ, hδone, hδsmall⟩ := (hpos.and (hone.and hsmall)).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hL δ hδ) _ hhalf] with n hn
  exact (hsplit δ hδ hδone n).trans
    ((add_le_add hδsmall hn).trans (ENNReal.add_halves ε).le)

end Problem367.RowEnergyCutoff

end

end OAI
