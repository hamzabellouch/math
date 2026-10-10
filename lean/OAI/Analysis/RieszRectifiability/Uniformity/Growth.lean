import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SeparatedSupportNets
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Packing.EuclideanPackingBound

namespace OAI

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_total_mass_of_bounded_support {d n : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hAD : ADRegularWithConstant n C μ)
    (hpos : μ.support.Nontrivial) (hfin : ediam μ.support ≠ ⊤) :
    μ Set.univ ≤ ENNReal.ofReal ((9 : ℝ) ^ d * C * (diam μ.support / 2) ^ n) := by
  classical
  let D := diam μ.support
  have hb : Bornology.IsBounded μ.support := isBounded_iff_ediam_ne_top.mpr hfin
  have hD : 0 < D := diam_pos hpos hb
  have hc : IsCompact μ.support := isCompact_iff_isClosed_bounded.mpr ⟨μ.isClosed_support, hb⟩
  obtain ⟨N, _, hNE, hsep, hcover⟩ := exists_separated_cover_extension μ.support ∅
    (D / 4) (by positivity) (empty_subset _) (by simp)
  have hNfin : N.Finite := by
    have h := separated_set_finite_inter_compact N μ.support (D / 4)
      (by positivity) hsep hc
    simpa only [inter_eq_left.mpr hNE] using! h
  let s := hNfin.toFinset
  obtain ⟨a, ha⟩ := hpos.nonempty
  let t := s.image (fun x => x - a)
  have hcard : t.card = s.card := Finset.card_image_of_injective _ (fun x y h => sub_left_inj.mp h)
  have hball : ∀ x ∈ t, ‖x‖ ≤ D := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem hb (hNE (hNfin.mem_toFinset.mp hy)) ha
  have hsep' : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 2 * (D / 8) ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    rw [dist_sub_right]
    have hn : z ≠ w := by rintro rfl; exact hxy rfl
    have hh := hsep (hNfin.mem_toFinset.mp hz) (hNfin.mem_toFinset.mp hw) hn
    linarith
  have hs : (s.card : ℝ) ≤ (9 : ℝ) ^ d := by
    have hp := euclidean_separated_card_le t D (D / 8) hD.le (by positivity) hball hsep'
    have heq : (D + D / 8) / (D / 8) = 9 := by field_simp; ring
    simpa only [hcard, heq] using! hp
  have hadmiss : AdmissibleRadius μ (D / 2) := by
    refine ⟨by positivity, ?_⟩
    calc
      ENNReal.ofReal (D / 2) ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ediam μ.support := ENNReal.ofReal_toReal hfin
  have hcov : μ.support ⊆ ⋃ x ∈ s, ball x (D / 2) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := hcover y hy
    exact mem_iUnion₂.mpr ⟨x, hNfin.mem_toFinset.mpr hx, lt_trans hyx (by linarith)⟩
  have heq : μ μ.support = μ Set.univ := by
    simpa only [univ_inter] using! (measure_inter_conull (μ := μ) (s := Set.univ) μ.measure_compl_support)
  calc
    μ Set.univ = μ μ.support := heq.symm
    _ ≤ μ (⋃ x ∈ s, ball x (D / 2)) := measure_mono hcov
    _ ≤ ∑ x ∈ s, μ (ball x (D / 2)) := measure_biUnion_finset_le s _
    _ ≤ ∑ _x ∈ s, ENNReal.ofReal (C * (D / 2) ^ n) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (hAD.2 x (hNE (hNfin.mem_toFinset.mp hx)) _ hadmiss).2
    _ = ENNReal.ofReal ((s.card : ℝ) * (C * (D / 2) ^ n)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : 0 ≤ (s.card : ℝ)), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (9 ^ d * C * (D / 2) ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      have hC : 0 ≤ C := zero_le_one.trans hAD.1
      nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ D / 2) n))]

theorem quantitative_global_growth {d n : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (C : ℝ) (hAD : ADRegularWithConstant n C μ)
    (hpos : μ.support.Nontrivial) :
    GlobalUpperGrowth n ((9 : ℝ) ^ d * C) μ := by
  have hC : 0 ≤ C := zero_le_one.trans hAD.1
  have hG : 0 ≤ (9 : ℝ) ^ d * C := mul_nonneg (by positivity) hC
  refine ⟨hG, ?_⟩
  intro a r hr
  by_cases hz : μ (ball a r) = 0
  · rw [hz]
    exact zero_le
  obtain ⟨x, hxa, hx⟩ := μ.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hz)
  by_cases hsmall : ENNReal.ofReal (2 * r) ≤ ediam μ.support
  · have hsub : ball a r ⊆ ball x (2 * r) := by
      intro y hy
      change dist y x < 2 * r
      calc
        dist y x ≤ dist y a + dist a x := dist_triangle _ _ _
        _ < r + r := add_lt_add hy (by simpa only [mem_ball, dist_comm] using! hxa)
        _ = 2 * r := by ring
    have hpow : (2 : ℝ) ^ n ≤ 9 ^ d :=
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 9) n).trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9) hnd)
    calc
      μ (ball a r) ≤ μ (ball x (2 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) := (hAD.2 x hx _ ⟨by positivity, hsmall⟩).2
      _ ≤ ENNReal.ofReal (9 ^ d * C * r ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow]
        nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hC (pow_nonneg hr.le n))]
  · have hdiam : ediam μ.support < ENNReal.ofReal (2 * r) := lt_of_not_ge hsmall
    have hfin : ediam μ.support ≠ ⊤ := ne_top_of_lt hdiam
    have hdr : diam μ.support < 2 * r := by
      have h := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hdiam
      simpa only [diam, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)] using! h
    calc
      μ (ball a r) ≤ μ Set.univ := measure_mono (subset_univ _)
      _ ≤ ENNReal.ofReal (9 ^ d * C * (diam μ.support / 2) ^ n) :=
        quantitative_total_mass_of_bounded_support μ C hAD hpos hfin
      _ ≤ ENNReal.ofReal (9 ^ d * C * r ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg diam_nonneg (by norm_num)) (by linarith) n) hG

end
end RieszRectifiability

end OAI
