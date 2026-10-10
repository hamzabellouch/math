import Mathlib
import OAI.Combinatorics.HoneycombCorridor.BridgeFiniteness

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem bridgeMean_eq_tsum (h : ℕ) :
    bridgeMean h = ∑' p : BridgePath h, firstLengthWeight p / bridgeMass h := by
  simp only [bridgeMean, bridgeLengthMass, tsum_div_const]

theorem confinedMean_eq_tsum (h : ℕ) :
    confinedMean h = ∑' p : ConfinedBridgePath h,
      firstLengthWeight p.val / confinedMass h := by
  simp only [confinedMean, confinedLengthMass, tsum_div_const]

theorem Subpower.div {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Subpower f a) (hg : Subpower g b) :
    Subpower (fun h => f h / g h) (a - b) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with h hfh hgh using div_pos hfh hgh
  · apply (hf.2.sub hg.2).congr'
    filter_upwards [hf.1, hg.1] with h hfh hgh
    rw [Real.log_div (ne_of_gt hfh) (ne_of_gt hgh), sub_div]

theorem bridgeMean_subpower_of_masses
    (hm : Subpower bridgeMass (-(1 : ℝ) / 4))
    (hl : Subpower bridgeLengthMass ((13 : ℝ) / 12)) :
    Subpower bridgeMean ((4 : ℝ) / 3) := by
  have h := hl.div hm
  norm_num at h
  exact h

theorem confinedMean_subpower_of_masses
    (hm : Subpower confinedMass (-(1 : ℝ) / 4))
    (hl : Subpower confinedLengthMass ((13 : ℝ) / 12)) :
    Subpower confinedMean ((4 : ℝ) / 3) := by
  have h := hl.div hm
  norm_num at h
  exact h

noncomputable def BridgeReachesDistance {h : ℕ} (t : ℝ) (p : BridgePath h) : Prop :=
  ∃ v ∈ p.vertices, t ≤ |(position v).1|

noncomputable def bridgeTailMass (h : ℕ) (t : ℝ) : ℝ := by
  classical
  exact ∑' p : BridgePath h, if BridgeReachesDistance t p then weight p else 0

noncomputable def bridgeTailLengthMass (h : ℕ) (t : ℝ) : ℝ := by
  classical
  exact ∑' p : BridgePath h,
    if BridgeReachesDistance t p then firstLengthWeight p else 0

@[simp] theorem reachesDistance_bridgeWord (h : ℕ) (hh : 1 ≤ h)
    (t : ℝ) (p : BridgePath h) :
    reachesDistance t (bridgeWord h hh p) ↔ BridgeReachesDistance t p := by
  simp only [reachesDistance, BridgeReachesDistance, bridgeWord_trace]

theorem weight_nonneg {h : ℕ} (p : BridgePath h) : 0 ≤ weight p :=
  pow_nonneg criticalActivity_pos.le _

theorem firstLengthWeight_nonneg {h : ℕ} (p : BridgePath h) :
    0 ≤ firstLengthWeight p :=
  mul_nonneg (Nat.cast_nonneg _) (weight_nonneg p)

theorem bridgeTailMass_le (h : ℕ) (hh : 1 ≤ h) (t : ℝ) (ht : 0 ≤ t) :
    bridgeTailMass h t ≤ tailConstant * Real.exp (-tailRate * t / (h + 1)) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro p
    exact ite_nonneg (weight_nonneg p) le_rfl
  · intro S
    obtain ⟨M, hM⟩ := bridge_finite_sum_word_bound h hh S
      (fun w => if reachesDistance t w then criticalActivity ^ w.length else 0)
      (fun w => ite_nonneg (pow_nonneg criticalActivity_pos.le _) le_rfl)
    simp only [reachesDistance_bridgeWord, bridgeWord_length] at hM
    exact hM.trans (lateralMass_exp h hh _ (vertexWindow_convex h M)
      (bottomSource_mem_window h M hh) (vertexWindow_strip h M) t ht)

theorem bridgeTailLengthMass_le (h : ℕ) (hh : 1 ≤ h) (t : ℝ) (ht : 0 ≤ t) :
    bridgeTailLengthMass h t ≤ tailConstant * spatialConstant * ((h : ℝ) + 1)^2 *
      Real.exp (-(tailRate / 2) * t / (h + 1)) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro p
    exact ite_nonneg (firstLengthWeight_nonneg p) le_rfl
  · intro S
    obtain ⟨M, hM⟩ := bridge_finite_sum_word_bound h hh S
      (fun w => if reachesDistance t w then
        (w.length : ℝ) * criticalActivity ^ w.length else 0)
      (fun w => ite_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _)) le_rfl)
    simp only [reachesDistance_bridgeWord, bridgeWord_length] at hM
    exact hM.trans (lateralLengthMass_exp h hh _ (vertexWindow_convex h M)
      (bottomSource_mem_window h M hh) (vertexWindow_strip h M) t ht)

theorem not_InLogCorridor_reaches {h : ℕ} (p : BridgePath h)
    (hp : ¬InLogCorridor p) :
    BridgeReachesDistance ((h : ℝ) * (Real.log (h : ℝ))^2) p := by
  classical
  by_contra hn
  apply hp
  intro v hv
  exact (lt_of_not_ge (fun hn' => hn ⟨v, hv, hn'⟩)).le

open scoped Classical

theorem logCorridor_loss_le {h : ℕ} (f : BridgePath h → ℝ)
    (hf : Summable f) (hf0 : ∀ p, 0 ≤ f p) :
    0 ≤ (∑' p, f p) - (∑' p : ConfinedBridgePath h, f p.val) ∧
    (∑' p, f p) - (∑' p : ConfinedBridgePath h, f p.val) ≤
      ∑' p, if BridgeReachesDistance ((h : ℝ) * (Real.log (h : ℝ))^2) p
        then f p else 0 := by
  classical
  let s : Set (BridgePath h) := {p | InLogCorridor p}
  let t : Set (BridgePath h) :=
    {p | BridgeReachesDistance ((h : ℝ) * (Real.log (h : ℝ))^2) p}
  change 0 ≤ (∑' p, f p) - (∑' p : s, f p.val) ∧
    (∑' p, f p) - (∑' p : s, f p.val) ≤ ∑' p, t.indicator f p
  rw [tsum_subtype, ← hf.tsum_sub (hf.indicator s)]
  have hnonneg : ∀ p, 0 ≤ f p - s.indicator f p := by
    intro p
    by_cases hp : InLogCorridor p
    · simp [s, hp]
    · simpa [s, hp] using hf0 p
  refine ⟨tsum_nonneg hnonneg, ?_⟩
  apply Summable.tsum_le_tsum _ (hf.sub (hf.indicator s)) (hf.indicator t)
  intro p
  by_cases hp : InLogCorridor p
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, s, hp, ite_true, sub_self]
    exact ite_nonneg (hf0 p) le_rfl
  · have ht := not_InLogCorridor_reaches p hp
    simp [s, t, hp, ht]

theorem logCorridor_mass_error (h : ℕ) (hh : 1 ≤ h) :
    0 ≤ bridgeMass h - confinedMass h ∧
    bridgeMass h - confinedMass h ≤ tailConstant *
      Real.exp (-tailRate * ((h : ℝ) * (Real.log (h : ℝ))^2) / (h + 1)) := by
  have he := logCorridor_loss_le (weight (h := h))
    (bridge_weight_summable h hh) weight_nonneg
  exact ⟨he.1, he.2.trans (bridgeTailMass_le h hh _ (by positivity))⟩

theorem logCorridor_length_error (h : ℕ) (hh : 1 ≤ h) :
    0 ≤ bridgeLengthMass h - confinedLengthMass h ∧
    bridgeLengthMass h - confinedLengthMass h ≤
      tailConstant * spatialConstant * ((h : ℝ) + 1)^2 *
      Real.exp (-(tailRate / 2) * ((h : ℝ) * (Real.log (h : ℝ))^2) / (h + 1)) := by
  have he := logCorridor_loss_le (firstLengthWeight (h := h))
    (bridge_length_summable h hh) firstLengthWeight_nonneg
  exact ⟨he.1, he.2.trans (bridgeTailLengthMass_le h hh _ (by positivity))⟩

theorem tendsto_rpow_mul_logGaussian {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Filter.Tendsto (fun h : ℕ => (h : ℝ)^a *
      Real.exp (-c * (Real.log (h : ℝ))^2)) Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun h : ℕ => Real.log (h : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hneg := Filter.tendsto_neg_atTop_atBot.comp (hlog.const_mul_atTop hc)
  have hdiff : Filter.Tendsto (fun h : ℕ => a - c * Real.log (h : ℝ))
      Filter.atTop Filter.atBot := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      (Filter.Tendsto.add_atBot (tendsto_const_nhds (x := a)) hneg)
  have hprod := hlog.atTop_mul_atBot₀ hdiff
  apply (Real.tendsto_exp_atBot.comp hprod).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  have hp : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  change Real.exp (Real.log (h : ℝ) * (a - c * Real.log (h : ℝ))) = _
  rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
  apply congrArg Real.exp
  ring

theorem tendsto_rpow_mul_logTailExp {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Filter.Tendsto (fun h : ℕ => (h : ℝ)^a *
      Real.exp (-c * ((h : ℝ) * (Real.log (h : ℝ))^2) / (h + 1)))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' _ _ (tendsto_rpow_mul_logGaussian (half_pos hc) a)
  · exact Filter.Eventually.of_forall (fun h =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg h) a) (Real.exp_pos _).le)
  · filter_upwards [Filter.eventually_ge_atTop 1] with h hh
    have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hH : 0 < (h : ℝ) + 1 := by positivity
    have hfrac : (1 / 2 : ℝ) ≤ (h : ℝ) / (h + 1) := by
      apply (le_div_iff₀ hH).mpr
      linarith
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg h) a)
    apply Real.exp_le_exp.mpr
    have hi := mul_le_mul_of_nonpos_left hfrac
      (neg_nonpos.mpr (mul_nonneg hc.le (sq_nonneg (Real.log (h : ℝ)))))
    convert hi using 1 <;> first | rfl | ring

theorem logCorridor_mass_error_superpolynomial (a : ℝ) :
    Filter.Tendsto (fun h : ℕ =>
      (bridgeMass h - confinedMass h) * (h : ℝ)^a)
      Filter.atTop (nhds 0) := by
  have ht := (tendsto_rpow_mul_logTailExp tailRate_pos a).const_mul tailConstant
  rw [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [Filter.eventually_ge_atTop 1] with h hh
    exact mul_nonneg (logCorridor_mass_error h hh).1
      (Real.rpow_nonneg (Nat.cast_nonneg h) a)
  · filter_upwards [Filter.eventually_ge_atTop 1] with h hh
    have he := mul_le_mul_of_nonneg_right (logCorridor_mass_error h hh).2
      (Real.rpow_nonneg (Nat.cast_nonneg h) a)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using he

theorem logCorridor_length_error_superpolynomial (a : ℝ) :
    Filter.Tendsto (fun h : ℕ =>
      (bridgeLengthMass h - confinedLengthMass h) * (h : ℝ)^a)
      Filter.atTop (nhds 0) := by
  have ht := (tendsto_rpow_mul_logTailExp (half_pos tailRate_pos) (a + 2)).const_mul
    (4 * tailConstant * spatialConstant)
  rw [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [Filter.eventually_ge_atTop 1] with h hh
    exact mul_nonneg (logCorridor_length_error h hh).1
      (Real.rpow_nonneg (Nat.cast_nonneg h) a)
  · filter_upwards [Filter.eventually_ge_atTop 1] with h hh
    have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hp : 0 < (h : ℝ) := by linarith
    have hsq : ((h : ℝ) + 1)^2 ≤ 4 * (h : ℝ)^2 := by nlinarith
    have he := mul_le_mul_of_nonneg_right (logCorridor_length_error h hh).2
      (Real.rpow_nonneg (Nat.cast_nonneg h) a)
    apply he.trans
    rw [Real.rpow_add hp, Real.rpow_two]
    calc
      _ ≤ tailConstant * spatialConstant * (4 * (h : ℝ)^2) *
          Real.exp (-(tailRate / 2) * ((h : ℝ) * (Real.log (h : ℝ))^2) / (h + 1)) *
          (h : ℝ)^a := by
        gcongr
        exact mul_nonneg tailConstant_pos.le spatialConstant_pos.le
      _ = _ := by ring

theorem Subpower.eventually_rpow_le {f : ℕ → ℝ} {a b : ℝ}
    (hf : Subpower f a) (hb : b < a) :
    ∀ᶠ h : ℕ in Filter.atTop, (h : ℝ)^b ≤ f h := by
  have he := hf.2.eventually (lt_mem_nhds hb)
  filter_upwards [hf.1, he, Filter.eventually_ge_atTop 2] with h hp he hh
  have hh' : (1 : ℝ) < h := by exact_mod_cast (show 1 < h by omega)
  have hpos : 0 < (h : ℝ) := lt_trans zero_lt_one hh'
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hpos b) hp).mp
  rw [Real.log_rpow hpos]
  exact ((le_div_iff₀ (Real.log_pos hh')).mp he.le)

theorem Subpower.error_div_tendsto_zero {f e : ℕ → ℝ} {a : ℝ}
    (hf : Subpower f a) (he0 : ∀ᶠ h in Filter.atTop, 0 ≤ e h)
    (he : ∀ b : ℝ, Filter.Tendsto (fun h : ℕ => e h * (h : ℝ)^b)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun h => e h / f h) Filter.atTop (nhds 0) := by
  apply squeeze_zero' _ _ (he (1 - a))
  · filter_upwards [hf.1, he0] with h hf he using div_nonneg he hf.le
  · filter_upwards [hf.eventually_rpow_le (show a - 1 < a by linarith),
      he0, Filter.eventually_ge_atTop 1] with h hb he0 hh
    have hp : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
    calc
      e h / f h ≤ e h / (h : ℝ)^(a - 1) :=
        div_le_div_of_nonneg_left he0 (Real.rpow_pos_of_pos hp _) hb
      _ = e h * (h : ℝ)^(1 - a) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hp.le]
        congr 2
        ring

theorem Subpower.of_ratio {f g : ℕ → ℝ} {a : ℝ} (hg : Subpower g a)
    (hr : Filter.Tendsto (fun h => f h / g h) Filter.atTop (nhds 1)) :
    Subpower f a := by
  have hf : ∀ᶠ h in Filter.atTop, 0 < f h := by
    filter_upwards [hg.1, hr.eventually (lt_mem_nhds zero_lt_one)] with h hg hr
    exact (div_pos_iff_of_pos_right hg).mp hr
  refine ⟨hf, ?_⟩
  have hlog : Filter.Tendsto (fun h : ℕ => Real.log (h : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Filter.Tendsto (fun h => Real.log (f h / g h) / Real.log (h : ℝ))
      Filter.atTop (nhds 0) := (hr.log one_ne_zero).div_atTop hlog
  have hsum := hg.2.add hratio
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [hf, hg.1] with h hf hg
  rw [Real.log_div (ne_of_gt hf) (ne_of_gt hg)]
  ring

theorem subpower_iff_of_superpolynomial_error {f g : ℕ → ℝ} {a : ℝ}
    (he0 : ∀ᶠ h in Filter.atTop, 0 ≤ f h - g h)
    (he : ∀ b : ℝ, Filter.Tendsto (fun h : ℕ => (f h - g h) * (h : ℝ)^b)
      Filter.atTop (nhds 0)) :
    Subpower f a ↔ Subpower g a := by
  constructor
  · intro hf
    have hd := hf.error_div_tendsto_zero he0 he
    apply hf.of_ratio
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hd
    rw [sub_zero] at ht
    apply ht.congr'
    filter_upwards [hf.1] with h hh
    field_simp
    ring
  · intro hg
    have hd := hg.error_div_tendsto_zero he0 he
    apply hg.of_ratio
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hd
    rw [add_zero] at ht
    apply ht.congr'
    filter_upwards [hg.1] with h hh
    field_simp
    ring

theorem confinedMass_subpower_iff (a : ℝ) :
    Subpower confinedMass a ↔ Subpower bridgeMass a := by
  symm
  apply subpower_iff_of_superpolynomial_error
    _ logCorridor_mass_error_superpolynomial
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  exact (logCorridor_mass_error h hh).1

theorem confinedLengthMass_subpower_iff (a : ℝ) :
    Subpower confinedLengthMass a ↔ Subpower bridgeLengthMass a := by
  symm
  apply subpower_iff_of_superpolynomial_error
    _ logCorridor_length_error_superpolynomial
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  exact (logCorridor_length_error h hh).1

end PolynomialVacuumBridge.Corridor

end

end OAI
