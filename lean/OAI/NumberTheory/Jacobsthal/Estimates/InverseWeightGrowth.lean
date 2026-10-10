import OAI.NumberTheory.Jacobsthal.Paths.FiniteHistorySupport
import OAI.NumberTheory.Jacobsthal.Renewal.WeightDickmanComparison

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightTailBounds

open Filter Set
open scoped Topology
open DerivativeWeights WeightDickmanComparison

theorem ratio_upper_from_rho {s c C p q : ℝ} (hs : 4 ≤ s)
    (hc : 0 < c) (hC : 0 < C) (hp : 0 < p)
    (hpl : c * Dickman.rho (s - 2) ≤ p) (hqu : q ≤ C * Dickman.rho (s - 3)) :
    q / p ≤ (4 * C / c) * s ^ 2 := by
  have hr : Dickman.rho (s - 3) ≤ 4 * (s - 2) ^ 2 * Dickman.rho (s - 2) := by
    convert! Dickman.rho_lower_comparison (u := s - 2) (by linarith) using 1
    congr 1
    ring
  have hr' : Dickman.rho (s - 3) ≤ 4 * s ^ 2 * Dickman.rho (s - 2) := by
    apply le_trans hr
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Dickman.rho_nonneg _)
  have hρ : Dickman.rho (s - 2) ≤ p / c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hq : q ≤ ((4 * C / c) * s ^ 2) * p := by
    calc
      q ≤ C * Dickman.rho (s - 3) := hqu
      _ ≤ C * (4 * s ^ 2 * Dickman.rho (s - 2)) := mul_le_mul_of_nonneg_left hr' hC.le
      _ ≤ C * (4 * s ^ 2 * (p / c)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hρ (by positivity)) hC.le
      _ = _ := by ring
  exact (div_le_iff₀ hp).mpr hq

theorem weights_ratio_bound : ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 4 ≤ s →
    phiOdd (s - 1) / phiEven s ≤ K * s ^ 2 ∧
    phiEven (s - 1) / phiOdd s ≤ K * s ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := weights_dickman_bounds
  refine ⟨4 * C / c, by positivity, ?_⟩
  intro s hs
  have hsp : 2 ≤ s - 1 := by linarith
  have he := (hb (s - 1) hsp).1.2
  have ho := (hb (s - 1) hsp).2.2
  rw [show s - 1 - 2 = s - 3 by ring] at he ho
  exact ⟨ratio_upper_from_rho hs hc hC (phiEven_pos (by linarith)) (hb s (by linarith)).1.1 ho,
    ratio_upper_from_rho hs hc hC (phiOdd_pos s) (hb s (by linarith)).2.1 he⟩

theorem even_logDeriv_eq {s : ℝ} (hs : 1 < s) :
    -deriv phiEven s / phiEven s = s / (s - 1) ^ 2 * (phiOdd (s - 1) / phiEven s) := by
  rw [(phiEven_hasDerivAt hs).deriv]
  ring

theorem odd_logDeriv_eq {s : ℝ} (hs : 3 < s) :
    -deriv phiOdd s / phiOdd s = s / (s - 1) ^ 2 * (phiEven (s - 1) / phiOdd s) := by
  rw [(phiOdd_hasDerivAt hs).deriv]
  ring

theorem weights_logDeriv_upper : ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 4 ≤ s →
    (0 ≤ -deriv phiEven s / phiEven s ∧ -deriv phiEven s / phiEven s ≤ K * s ^ 3) ∧
    (0 ≤ -deriv phiOdd s / phiOdd s ∧ -deriv phiOdd s / phiOdd s ≤ K * s ^ 3) := by
  obtain ⟨K, hK, hb⟩ := weights_ratio_bound
  refine ⟨K, hK, ?_⟩
  intro s hs
  have hs1 : 1 < s := by linarith
  have hs3 : 3 < s := by linarith
  rw [even_logDeriv_eq hs1, odd_logDeriv_eq hs3]
  have hcoeff : s / (s - 1) ^ 2 ≤ s := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
    nlinarith
  have hcoeff0 : 0 ≤ s / (s - 1) ^ 2 := by positivity
  have he0 : 0 ≤ phiOdd (s - 1) / phiEven s :=
    (div_pos (phiOdd_pos _) (phiEven_pos hs1)).le
  have ho0 : 0 ≤ phiEven (s - 1) / phiOdd s :=
    (div_pos (phiEven_pos (by linarith)) (phiOdd_pos s)).le
  constructor
  · refine ⟨mul_nonneg hcoeff0 he0, ?_⟩
    calc
      _ ≤ s * (K * s ^ 2) := mul_le_mul hcoeff (hb s hs).1 he0 (by linarith)
      _ = _ := by ring
  · refine ⟨mul_nonneg hcoeff0 ho0, ?_⟩
    calc
      _ ≤ s * (K * s ^ 2) := mul_le_mul hcoeff (hb s hs).2 ho0 (by linarith)
      _ = _ := by ring

theorem slope_lower_from_rho {s c C p q : ℝ} (hs : 4 ≤ s)
    (hc : 0 < c) (hC : 0 < C) (hp : 0 < p)
    (hpu : p ≤ C * Dickman.rho (s - 2)) (hql : c * Dickman.rho (s - 3) ≤ q) :
    (c / (2 * C)) * DickmanDecay.hazard (s - 2) ≤
      s / (s - 1) ^ 2 * (q / p) := by
  have hnum : 0 ≤ c * Dickman.rho (s - 3) := (mul_pos hc (Dickman.rho_pos _)).le
  have hratio : (c * Dickman.rho (s - 3)) / (C * Dickman.rho (s - 2)) ≤ q / p := by
    calc
      _ ≤ (c * Dickman.rho (s - 3)) / p := div_le_div_of_nonneg_left hnum hp hpu
      _ ≤ q / p := div_le_div_of_nonneg_right hql hp.le
  have hcoeff : 1 / (2 * (s - 2)) ≤ s / (s - 1) ^ 2 := by
    apply (div_le_div_iff₀ (by linarith : 0 < 2 * (s - 2)) (sq_pos_of_pos (by linarith))).mpr
    nlinarith
  have hbase : 0 ≤ (c * Dickman.rho (s - 3)) / (C * Dickman.rho (s - 2)) :=
    (div_pos (mul_pos hc (Dickman.rho_pos _)) (mul_pos hC (Dickman.rho_pos _))).le
  calc
    _ = (1 / (2 * (s - 2))) * ((c * Dickman.rho (s - 3)) / (C * Dickman.rho (s - 2))) := by
      unfold DickmanDecay.hazard
      rw [show s - 2 - 1 = s - 3 by ring]
      field_simp
    _ ≤ _ := mul_le_mul hcoeff hratio hbase (by positivity)

theorem weights_logDeriv_ge_hazard : ∃ k : ℝ, 0 < k ∧ ∀ s : ℝ, 4 ≤ s →
    k * DickmanDecay.hazard (s - 2) ≤ -deriv phiEven s / phiEven s ∧
    k * DickmanDecay.hazard (s - 2) ≤ -deriv phiOdd s / phiOdd s := by
  obtain ⟨c, C, hc, hC, hb⟩ := weights_dickman_bounds
  refine ⟨c / (2 * C), by positivity, ?_⟩
  intro s hs
  have hsp : 2 ≤ s - 1 := by linarith
  have he := (hb (s - 1) hsp).1.1
  have ho := (hb (s - 1) hsp).2.1
  rw [show s - 1 - 2 = s - 3 by ring] at he ho
  rw [even_logDeriv_eq (by linarith), odd_logDeriv_eq (by linarith)]
  exact ⟨slope_lower_from_rho hs hc hC (phiEven_pos (by linarith)) (hb s (by linarith)).1.2 ho,
    slope_lower_from_rho hs hc hC (phiOdd_pos s) (hb s (by linarith)).2.2 he⟩

theorem weights_logDeriv_growth (rate : ℝ) : ∃ U : ℝ, 4 ≤ U ∧ ∀ s : ℝ, U ≤ s →
    rate ≤ -deriv phiEven s / phiEven s ∧ rate ≤ -deriv phiOdd s / phiOdd s := by
  obtain ⟨k, hk, hkb⟩ := weights_logDeriv_ge_hazard
  obtain ⟨T, hT, ht⟩ := DickmanDecay.exists_hazard_tail (rate / k)
  refine ⟨T + 2, by linarith, ?_⟩
  intro s hs
  have h : rate ≤ k * DickmanDecay.hazard (s - 2) := by
    have ht' := mul_le_mul_of_nonneg_left (ht (s - 2) (by linarith)) hk.le
    have heq : k * (rate / k) = rate := by field_simp
    rwa [heq] at ht'
  exact ⟨le_trans h (hkb s (by linarith)).1, le_trans h (hkb s (by linarith)).2⟩

end NumberTheoryLean.WeightTailBounds

end

section

namespace NumberTheoryLean.WeightGlobalBounds

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge DerivativeWeights WeightTailBounds

theorem weights_global_ratio_bound : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℝ, 198 / 100 ≤ s → phiOdd (s - 1) / phiEven s ≤ C * (1 + s) ^ 2) ∧
    (∀ s : ℝ, 95 / 100 ≤ s → phiEven (max 2 (s - 1)) / phiOdd s ≤ C * (1 + s) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := weights_ratio_bound
  let E : ℝ := sieveA / phiEven 4
  let O : ℝ := phiEven 2 / phiOdd 4
  have hE : 0 < E := div_pos sieveA_pos (phiEven_pos (by norm_num))
  have hO : 0 < O := div_pos (phiEven_pos (by norm_num)) (phiOdd_pos 4)
  let C := K + E + O
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  have hOC : O ≤ C := by dsimp [C]; linarith
  have hlarge : ∀ s : ℝ, 0 ≤ s → K * s ^ 2 ≤ C * (1 + s) ^ 2 := by
    intro s hs
    exact mul_le_mul hKC (by nlinarith) (sq_nonneg _) hC.le
  have hsmall : ∀ s : ℝ, 0 ≤ s → C ≤ C * (1 + s) ^ 2 := by
    intro s hs
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (1 + s) ^ 2 by nlinarith) hC.le]
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    have hs1 : 1 < s := by linarith
    by_cases hs4 : s ≤ 4
    · have hden : phiEven 4 ≤ phiEven s :=
        phiEven_strictAntiOn.antitoneOn hs1 (by norm_num) hs4
      rw [phiOdd_initial (s := s - 1) (by linarith)]
      exact le_trans (div_le_div_of_nonneg_left sieveA_pos.le (phiEven_pos (by norm_num)) hden)
        (le_trans hEC (hsmall s (by linarith)))
    · exact le_trans (hb s (le_of_not_ge hs4)).1 (hlarge s (by linarith))
  · intro s hs
    by_cases hs4 : s ≤ 4
    · have hm2 : 2 ≤ max 2 (s - 1) := le_max_left _ _
      have hnum : phiEven (max 2 (s - 1)) ≤ phiEven 2 :=
        phiEven_strictAntiOn.antitoneOn (by norm_num) (by change 1 < max 2 (s - 1); linarith) hm2
      have hden : phiOdd 4 ≤ phiOdd s := phiOdd_antitone hs4
      have hr : phiEven (max 2 (s - 1)) / phiOdd s ≤ O := by
        calc
          _ ≤ phiEven 2 / phiOdd s := div_le_div_of_nonneg_right hnum (phiOdd_pos s).le
          _ ≤ _ := div_le_div_of_nonneg_left (phiEven_pos (by norm_num)).le (phiOdd_pos 4) hden
      exact le_trans hr (le_trans hOC (hsmall s (by linarith)))
    · rw [max_eq_right (show 2 ≤ s - 1 by linarith)]
      exact le_trans (hb s (le_of_not_ge hs4)).2 (hlarge s (by linarith))

theorem weights_global_logDeriv_bound : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℝ, 198 / 100 ≤ s →
      |deriv phiEven s / phiEven s| ≤ C * (1 + s) ^ 3) ∧
    (∀ s : ℝ, 3 < s → |deriv phiOdd s / phiOdd s| ≤ C * (1 + s) ^ 3) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_ratio_bound
  refine ⟨4 * C, by positivity, ?_, ?_⟩
  · intro s hs
    have hs1 : 1 < s := by linarith
    have hcoeff : s / (s - 1) ^ 2 ≤ 4 * (1 + s) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
      have hsq : (1 : ℝ) / 4 ≤ (s - 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * (1 + s) by linarith)]
    have hr0 : 0 ≤ phiOdd (s - 1) / phiEven s :=
      (div_pos (phiOdd_pos _) (phiEven_pos hs1)).le
    have hn : 0 ≤ -deriv phiEven s / phiEven s := by rw [even_logDeriv_eq hs1]; positivity
    have habs : |deriv phiEven s / phiEven s| = -deriv phiEven s / phiEven s := by
      rw [abs_of_nonpos (by rw [neg_div] at hn; linarith)]
      ring
    rw [habs, even_logDeriv_eq hs1]
    calc
      _ ≤ (4 * (1 + s)) * (C * (1 + s) ^ 2) := mul_le_mul hcoeff (he s hs) hr0 (by linarith)
      _ = _ := by ring
  · intro s hs
    have hcoeff : s / (s - 1) ^ 2 ≤ 4 * (1 + s) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
      have hsq : 1 ≤ (s - 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * (1 + s) by linarith)]
    have hr : phiEven (s - 1) / phiOdd s ≤ C * (1 + s) ^ 2 := by
      have h := ho s (by linarith)
      rwa [max_eq_right (show 2 ≤ s - 1 by linarith)] at h
    have hr0 : 0 ≤ phiEven (s - 1) / phiOdd s :=
      (div_pos (phiEven_pos (by linarith)) (phiOdd_pos s)).le
    have hn : 0 ≤ -deriv phiOdd s / phiOdd s := by rw [odd_logDeriv_eq hs]; positivity
    have habs : |deriv phiOdd s / phiOdd s| = -deriv phiOdd s / phiOdd s := by
      rw [abs_of_nonpos (by rw [neg_div] at hn; linarith)]
      ring
    rw [habs, odd_logDeriv_eq hs]
    calc
      _ ≤ (4 * (1 + s)) * (C * (1 + s) ^ 2) := mul_le_mul hcoeff hr hr0 (by linarith)
      _ = _ := by ring

theorem interval_abs_bound {H d : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt H (d t) t)
    (hb : ∀ t ∈ Ioo a b, |d t| ≤ B) : |H b - H a| ≤ B * (b - a) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    simp
  · obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope H h hc
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    rw [(hd t ht).deriv] at heq
    have hbound := hb t ht
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr h)] at hbound
    exact (div_le_iff₀ (sub_pos.mpr h)).mp hbound

theorem phiOdd_max_three (s : ℝ) : phiOdd (max 3 s) = phiOdd s := by
  by_cases hs : s ≤ 3
  · rw [max_eq_left hs, phiOdd_initial le_rfl, phiOdd_initial hs]
  · rw [max_eq_right (le_of_not_ge hs)]

theorem weights_log_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    (∀ u v : ℝ, 198 / 100 ≤ u → 198 / 100 ≤ v → u ≤ S → v ≤ S →
      |Real.log (phiEven u) - Real.log (phiEven v)| ≤ C * (1 + S) ^ 3 * |u - v|) ∧
    (∀ u v : ℝ, 95 / 100 ≤ u → 95 / 100 ≤ v → u ≤ S → v ≤ S →
      |Real.log (phiOdd u) - Real.log (phiOdd v)| ≤ C * (1 + S) ^ 3 * |u - v|) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_logDeriv_bound
  refine ⟨C, hC, ?_⟩
  intro S hS
  have he_ordered : ∀ u v : ℝ, 198 / 100 ≤ u → u ≤ v → v ≤ S →
      |Real.log (phiEven v) - Real.log (phiEven u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
    intro u v hu huv hv
    apply interval_abs_bound huv
    · intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      exact ((phiEven_continuousAt ht1).log (ne_of_gt (phiEven_pos ht1))).continuousWithinAt
    · intro t ht
      exact ((phiEven_hasDerivAt (by linarith [ht.1])).differentiableAt.hasDerivAt.log
        (ne_of_gt (phiEven_pos (by linarith [ht.1]))))
    · intro t ht
      have h := he t (by linarith [ht.1])
      apply le_trans h
      apply mul_le_mul_of_nonneg_left _ hC.le
      gcongr <;> linarith [ht.1, ht.2]
  have ho_ordered : ∀ u v : ℝ, 3 ≤ u → u ≤ v → v ≤ S →
      |Real.log (phiOdd v) - Real.log (phiOdd u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
    intro u v hu huv hv
    apply interval_abs_bound huv
    · intro t _
      exact (phiOdd_continuous.continuousAt.log (ne_of_gt (phiOdd_pos t))).continuousWithinAt
    · intro t ht
      exact ((phiOdd_hasDerivAt (by linarith [ht.1])).differentiableAt.hasDerivAt.log
        (ne_of_gt (phiOdd_pos t)))
    · intro t ht
      have h := ho t (by linarith [ht.1])
      apply le_trans h
      apply mul_le_mul_of_nonneg_left _ hC.le
      gcongr <;> linarith [ht.1, ht.2]
  constructor
  · intro u v hu hv huS hvS
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm (Real.log (phiEven u)), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact he_ordered u v hu huv hvS
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact he_ordered v u hv hvu huS
  · have ho_clamped : ∀ u v : ℝ, u ≤ v → v ≤ S →
        |Real.log (phiOdd v) - Real.log (phiOdd u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
      intro u v huv hvS
      have hmax : max 3 u ≤ max 3 v := max_le_max_left 3 huv
      have hdiff : max 3 v - max 3 u ≤ v - u := by
        by_cases hu : u ≤ 3
        · rw [max_eq_left hu]
          by_cases hv : v ≤ 3
          · rw [max_eq_left hv]
            linarith
          · rw [max_eq_right (le_of_not_ge hv)]
            linarith
        · rw [max_eq_right (le_of_not_ge hu), max_eq_right (show 3 ≤ v by linarith)]
      have h := ho_ordered (max 3 u) (max 3 v) (le_max_left _ _) hmax (max_le hS hvS)
      rw [phiOdd_max_three, phiOdd_max_three] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hdiff (by positivity))
    intro u v _ _ huS hvS
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm (Real.log (phiOdd u)), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact ho_clamped u v huv hvS
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact ho_clamped v u hvu huS

theorem even_starting_derivative {s : ℝ} (hs : 198 / 100 ≤ s) (hs2 : s < 2) :
    phiEven s = s ^ 2 * deriv (startingExtension sieveA) s := by
  rw [(startingExtension_hasDerivAt (by linarith : 1 < s)).deriv, phiEven_initial hs2.le]
  field_simp

theorem phiOdd_deriv_initial {s : ℝ} (hs : s ≤ 3) : deriv phiOdd s = 0 := by
  by_cases hd : DifferentiableAt ℝ phiOdd s
  · have h0 : HasDerivWithinAt phiOdd 0 (Iic s) s := by
      apply (hasDerivAt_const s sieveA).hasDerivWithinAt.congr_of_mem
      · intro t ht
        exact phiOdd_initial (le_trans ht hs)
      · exact self_mem_Iic
    have h1 := hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic s)
    have h2 := h0.derivWithin (uniqueDiffWithinAt_Iic s)
    exact h1.symm.trans h2
  · exact deriv_zero_of_not_differentiableAt hd

theorem weights_global_logDeriv_bound_all : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℝ, 198 / 100 ≤ s → |deriv phiEven s / phiEven s| ≤ C * (1 + s) ^ 3) ∧
    (∀ s : ℝ, 95 / 100 ≤ s → |deriv phiOdd s / phiOdd s| ≤ C * (1 + s) ^ 3) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_logDeriv_bound
  refine ⟨C, hC, he, ?_⟩
  intro s hs
  by_cases hs3 : 3 < s
  · exact ho s hs3
  · rw [phiOdd_deriv_initial (le_of_not_gt hs3), zero_div, abs_zero]
    exact mul_nonneg hC.le (pow_nonneg (by linarith) 3)

end NumberTheoryLean.WeightGlobalBounds

end

section

namespace NumberTheoryLean.InverseWeightGrowth
open FinitePathGeometry DerivativeWeights WeightGlobalBounds

private def reference : Side → ℝ | .even => 2 | .odd => 1

private theorem reference_valid (i : Side) : Valid i (reference i) := by
  cases i <;> norm_num [reference,Valid]

private theorem reference_bounds (i : Side) : 0 ≤ reference i ∧ reference i ≤ 3 := by
  cases i <;> norm_num [reference]

theorem inverse_weight_quartic : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ i : Side, ∀ t : ℝ, Valid i t →
      1/weight i t ≤ A*Real.exp (C*(1+t)^4) := by
  obtain ⟨L,hL,hlocal⟩ := weights_log_lipschitz
  let A : ℝ := 1/weight .even 2 + 1/weight .odd 1
  have hE : 0 < 1/weight .even 2 := one_div_pos.mpr (weight_pos (by norm_num [Valid]))
  have hO : 0 < 1/weight .odd 1 := one_div_pos.mpr (weight_pos (by norm_num [Valid]))
  have hA : 0 < A := add_pos hE hO
  refine ⟨A,192*L,hA,by positivity,?_⟩
  intro i t ht
  have ht0 := valid_pos ht
  have hr := reference_valid i
  have hr0 := (reference_bounds i).1
  have hr3 := (reference_bounds i).2
  let S : ℝ := t+3
  have hS : 3 ≤ S := by dsimp [S]; linarith
  have htS : t ≤ S := by dsimp [S]; linarith
  have hrS : reference i ≤ S := by dsimp [S]; linarith
  have hlog : |Real.log (weight i (reference i))-Real.log (weight i t)| ≤
      L*(1+S)^3*|reference i-t| := by
    cases i with
    | even => exact (hlocal S hS).1 _ _ hr ht hrS htS
    | odd => exact (hlocal S hS).2 _ _ hr ht hrS htS
  have hdist : |reference i-t| ≤ 3*(1+t) := by
    calc
      _ ≤ |reference i|+|t| := abs_sub _ _
      _ = reference i+t := by rw [abs_of_nonneg hr0,abs_of_nonneg ht0.le]
      _ ≤ _ := by linarith
  have hSbound : 1+S ≤ 4*(1+t) := by dsimp [S]; linarith
  have hmajor : L*(1+S)^3*|reference i-t| ≤ (192*L)*(1+t)^4 := by
    calc
      _ ≤ L*(4*(1+t))^3*(3*(1+t)) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSbound 3) hL.le)
        hdist (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hdifference : Real.log (weight i (reference i))-Real.log (weight i t) ≤
      (192*L)*(1+t)^4 := ((le_abs_self _).trans hlog).trans hmajor
  have hexp := Real.exp_le_exp.mpr hdifference
  rw [Real.exp_sub,Real.exp_log (weight_pos hr),Real.exp_log (weight_pos ht)] at hexp
  have hreference : 1/weight i (reference i) ≤ A := by
    cases i <;> dsimp [reference,A] <;> linarith
  calc
    _ = (1/weight i (reference i))*(weight i (reference i)/weight i t) := by
      field_simp [(weight_pos hr).ne']
    _ ≤ (1/weight i (reference i))*Real.exp ((192*L)*(1+t)^4) :=
      mul_le_mul_of_nonneg_left hexp (one_div_nonneg.mpr (weight_pos hr).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hreference (Real.exp_pos _).le

theorem inverse_phi_quartic : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    (∀ t : ℝ, 198/100 ≤ t → 1/phiEven t ≤ A*Real.exp (C*(1+t)^4)) ∧
    (∀ t : ℝ, 95/100 ≤ t → 1/phiOdd t ≤ A*Real.exp (C*(1+t)^4)) := by
  obtain ⟨A,C,hA,hC,h⟩ := inverse_weight_quartic
  exact ⟨A,C,hA,hC,h .even,h .odd⟩

theorem inverse_weight_below_cutoff : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ K : ℝ, ∀ i : Side, ∀ t : ℝ, Valid i t → t ≤ K →
      1/weight i t ≤ A*Real.exp (C*(1+K)^4) := by
  obtain ⟨A,C,hA,hC,h⟩ := inverse_weight_quartic
  refine ⟨A,C,hA,hC,?_⟩
  intro K i t ht htK
  have ht0 := valid_pos ht
  exact (h i t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1+t) (by linarith : 1+t ≤ 1+K) 4) hC.le)) hA.le)

end NumberTheoryLean.InverseWeightGrowth

end

end Erdos970

end OAI
