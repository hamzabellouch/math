import OAI.GroupTheory.Thompson.AnalyticSinc
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

/-!
# Finite-region uniform separation

The generic results below separate the compactness and scalar estimates from
the concrete curve calculations. The actual analytic curve must supply every
listed identity and inequality before this result is used in the tube theorem.
-/

noncomputable section

universe uH

namespace ThompsonNonamenability.Analytic

open Set

theorem exists_uniform_sep_on_square
    {H : Type uH} [NormedAddCommGroup H]
    (γ : ℝ → H) (hcont : Continuous γ) (hinj : Function.Injective γ)
    (d : ℝ) (hd : 0 < d) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ s ∈ Icc (-4 : ℝ) 5,
      ∀ t ∈ Icc (-4 : ℝ) 5,
        d ≤ t - s → μ ≤ ‖γ t - γ s‖ := by
  let C : Set (ℝ × ℝ) :=
    (Icc (-4 : ℝ) 5 ×ˢ Icc (-4 : ℝ) 5) ∩ {p | d ≤ p.2 - p.1}
  have hclosed : IsClosed {p : ℝ × ℝ | d ≤ p.2 - p.1} :=
    isClosed_le continuous_const (continuous_snd.sub continuous_fst)
  have hcompact : IsCompact C :=
    ((isCompact_Icc : IsCompact (Icc (-4 : ℝ) 5)).prod isCompact_Icc).inter_right
      hclosed
  have hcontinuous : Continuous (fun p : ℝ × ℝ => ‖γ p.2 - γ p.1‖) :=
    ((hcont.comp continuous_snd).sub (hcont.comp continuous_fst)).norm
  have hpositive : ∀ p ∈ C, 0 < ‖γ p.2 - γ p.1‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro heq
    have hparam : p.2 = p.1 := hinj heq
    have hgap : d ≤ p.2 - p.1 := hp.2
    rw [hparam, sub_self] at hgap
    exact (not_le_of_gt hd) hgap
  obtain ⟨μ, hμ, hbound⟩ := hcompact.exists_forall_le'
    hcontinuous.continuousOn hpositive
  refine ⟨μ, hμ, ?_⟩
  intro s hs t ht hgap
  exact hbound (s, t) ⟨⟨hs, ht⟩, hgap⟩

theorem uniform_separation_of_five_regions
    {H : Type uH} [NormedAddCommGroup H]
    (γ : ℝ → H) (hcont : Continuous γ) (hinj : Function.Injective γ)
    (hline : ∀ s t : ℝ, s ≤ t → t ≤ 1 → ‖γ t - γ s‖ = (t - s) / 8)
    (hnegative : ∀ s t : ℝ, s ≤ -4 → 1 < t → 3 / 16 ≤ ‖γ t - γ s‖)
    (htail : ∀ s t : ℝ, 3 ≤ s → s ≤ t →
      ‖γ t - γ s‖ ^ 2 = 2 * (5 / 16 : ℝ) ^ 2 * (1 - sinc (t - s)))
    (hmixed : ∀ s t : ℝ, s ≤ 3 → 5 ≤ t →
      3 * (5 / 16 : ℝ) ^ 2 / 4 ≤ ‖γ t - γ s‖ ^ 2)
    (d : ℝ) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ ∀ s t : ℝ, d ≤ |t - s| → η ≤ ‖γ t - γ s‖ := by
  obtain ⟨ε, hε, hεhalf, hsinc⟩ := exists_uniform_sinc_gap d hd
  obtain ⟨μ, hμ, hcompact⟩ := exists_uniform_sep_on_square γ hcont hinj d hd
  let η : ℝ := min (d / 8) (min (3 / 16) (min ((5 / 16) * ε) (min (5 / 32) μ)))
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min (div_pos hd (by norm_num))
      (lt_min (by norm_num) (lt_min (mul_pos (by norm_num) hε)
        (lt_min (by norm_num) hμ)))
  have hηline : η ≤ d / 8 := min_le_left _ _
  have hηneg : η ≤ 3 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηtail : η ≤ (5 / 16) * ε :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηmixed : η ≤ 5 / 32 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hηcompact : η ≤ μ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hordered : ∀ s t : ℝ, d ≤ t - s → η ≤ ‖γ t - γ s‖ := by
    intro s t hgap
    have hst : s ≤ t := by linarith
    by_cases ht1 : t ≤ 1
    · rw [hline s t hst ht1]
      exact hηline.trans (by linarith)
    have ht1' : 1 < t := lt_of_not_ge ht1
    by_cases hsneg : s ≤ -4
    · exact hηneg.trans (hnegative s t hsneg ht1')
    by_cases hs3 : 3 ≤ s
    · have hsq : ((5 / 16 : ℝ) * ε) ^ 2 ≤ ‖γ t - γ s‖ ^ 2 := by
        rw [htail s t hs3 hst]
        have hepssq : ε ^ 2 ≤ 2 * ε := by
          nlinarith [mul_le_mul_of_nonneg_right hεhalf hε.le]
        have hgap' := hsinc (t - s) hgap
        nlinarith
      have hlow : (5 / 16 : ℝ) * ε ≤ ‖γ t - γ s‖ :=
        (sq_le_sq₀ (mul_nonneg (by norm_num) hε.le) (norm_nonneg _)).mp hsq
      exact hηtail.trans hlow
    by_cases ht5 : 5 ≤ t
    · have hsq : (5 / 32 : ℝ) ^ 2 ≤ ‖γ t - γ s‖ ^ 2 := by
        have hm := hmixed s t (le_of_not_ge hs3) ht5
        nlinarith
      have hlow : (5 / 32 : ℝ) ≤ ‖γ t - γ s‖ :=
        (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp hsq
      exact hηmixed.trans hlow
    · exact hηcompact.trans (hcompact s ⟨by linarith, by linarith⟩
        t ⟨by linarith, by linarith⟩ hgap)
  refine ⟨η, hηpos, ?_⟩
  intro s t hgap
  by_cases hst : s ≤ t
  · exact hordered s t (by simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hgap)
  · have hts : t ≤ s := (lt_of_not_ge hst).le
    have hgap' : d ≤ s - t := by
      simpa [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hgap
    simpa only [norm_sub_rev] using hordered t s hgap'

end ThompsonNonamenability.Analytic

end

end OAI
