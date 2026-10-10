import OAI.Probability.SATVariance.LifetimeSharpness

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

lemma sharp_parameters {k g : ℕ} (hg : 2 ≤ g) :
    g^(k+1) ≤ g^(k+2) ∧ k ≤ g^(k+1) ∧ 0 < g^(k+2) := by
  refine ⟨?_, ?_, by positivity⟩
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
      ((Nat.pow_le_pow_left hg k).trans (Nat.pow_le_pow_right (by omega) (by omega)))

lemma replacement_scaled_limit (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun g : ℕ => (g : ℝ)^(k-1) * blockKill (g^(k+2)) k
      (subcube (g^(k+2)) (g^(k+1))) g) atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by
  let h := fun g : ℕ => killRatio (g^(k+2)) (g^(k+1)) k
  have hlim : Tendsto (fun g : ℕ => (g : ℝ)^k * h g) atTop (𝓝 (((2 : ℝ)^k)⁻¹)) :=
    killRatio_limit (by omega : 0 < k+1) k
  have elo : Tendsto (fun g : ℕ => ((g : ℝ)^k * h g)^2 / (g : ℝ)^(k-1))
      atTop (𝓝 0) := (hlim.pow 2).div_atTop (tendsto_nat_pow_real (k-1) (by omega))
  have elo' : Tendsto (fun g : ℕ => (g : ℝ)^k * h g - ((g : ℝ)^k * h g)^2 / (g : ℝ)^(k-1))
      atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by simpa using hlim.sub elo
  have eup : Tendsto (fun g : ℕ => (g : ℝ)^k * h g + (k : ℝ)^2 / g)
      atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by
    simpa using hlim.add (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)^2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' elo' eup
  · filter_upwards [eventually_ge_atTop 2] with g hg
    obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
    have hl := mul_le_mul_of_nonneg_left (subcube_block_lower hbu (hkb.trans hbu) g)
      (pow_nonneg (Nat.cast_nonneg g) (k-1))
    have he : (g : ℝ)^(k-1) * ((g : ℝ) * h g - (g : ℝ)^2 * (h g)^2) =
        (g : ℝ)^k * h g - ((g : ℝ)^k * h g)^2 / (g : ℝ)^(k-1) := by
      have hg0 : (g : ℝ) ≠ 0 := by positivity
      have hk' : k = (k-1)+1 := by omega
      have hpow : (g : ℝ)^k = (g : ℝ)^(k-1) * g := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      rw [hpow]
      simp only [pow_succ]
      field_simp
    rwa [show killRatio (g^(k+2)) (g^(k+1)) k = h g from rfl, he] at hl
  · filter_upwards [eventually_ge_atTop 2] with g hg
    obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
    have hl := mul_le_mul_of_nonneg_left (subcube_block_upper hu hbu (hkb.trans hbu) g)
      (pow_nonneg (Nat.cast_nonneg g) (k-1))
    have he : (g : ℝ)^(k-1) * ((g : ℝ) * h g + (g : ℝ)^2 * (k : ℝ)^2 / (g^(k+2) : ℕ)) =
        (g : ℝ)^k * h g + (k : ℝ)^2 / g := by
      have hg0 : (g : ℝ) ≠ 0 := by positivity
      have hk' : k = (k-1)+1 := by omega
      have hk2 : k+2 = (k-1)+3 := by omega
      rw [hk2]
      have hpow : (g : ℝ)^k = (g : ℝ)^(k-1) * g := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      rw [hpow]
      push_cast
      simp only [pow_succ]
      field_simp
    rwa [show killRatio (g^(k+2)) (g^(k+1)) k = h g from rfl, he] at hl

lemma replacement_gap_scaled_limit (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun g : ℕ => (g : ℝ)^(k-1) *
      (blockKill (g^(k+2)) (k-1) (subcube (g^(k+2)) (g^(k+1))) 1 -
       blockKill (g^(k+2)) k (subcube (g^(k+2)) (g^(k+1))) g))
      atTop (𝓝 (((2 : ℝ)^k)⁻¹)) := by
  have hq := killRatio_limit (by omega : 0 < k+1) (k-1)
  have hr := replacement_scaled_limit k hk
  have hc : ((2 : ℝ)^(k-1))⁻¹ - ((2 : ℝ)^k)⁻¹ = ((2 : ℝ)^k)⁻¹ := by
    have he : k = (k-1)+1 := by omega
    conv_lhs => rhs; rw [he, pow_succ]
    conv_rhs => rw [he, pow_succ]
    field_simp
    ring
  have hh := hq.sub hr
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with g hg
  obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
  rw [subcube_one hbu (by omega : k-1 ≤ g^(k+2))]
  ring

theorem replacement_sharp (k : ℕ) (hk : 3 ≤ k) :
    ∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ))) := by
  refine ⟨fun g => g^(k+2), fun g => subcube (g^(k+2)) (g^(k+1)), ?_, ?_⟩
  · intro g hg
    obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
    exact ⟨hkb.trans hbu, subcube_nonempty _ _⟩
  · have hc : ((2 : ℝ)^k)⁻¹ ≠ 0 := by positivity
    apply (Asymptotics.isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_ge_atTop 2] with g hg
      exact mul_ne_zero hc (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))).mpr
    have hh := (replacement_gap_scaled_limit k hk).div_const (((2 : ℝ)^k)⁻¹)
    rw [div_self hc] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with g hg
    simp only [Pi.div_apply]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    field_simp

theorem no_uniform_littleO_error (k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g := by
  rintro ⟨e, he, hbound⟩
  have hc : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  have hp := (replacement_gap_scaled_limit k hk).eventually_const_lt (show
    ((2 : ℝ)^k)⁻¹ / 2 < ((2 : ℝ)^k)⁻¹ by linarith)
  have hsmall := he.tendsto_div_nhds_zero.eventually_lt_const (show
    (0 : ℝ) < ((2 : ℝ)^k)⁻¹ / 2 by positivity)
  obtain ⟨g, hg, hp, he'⟩ := ((eventually_ge_atTop 2).and (hp.and hsmall)).exists
  obtain ⟨hbu, hkb, hu⟩ := sharp_parameters (k := k) hg
  have hb := hbound (g^(k+2)) (hkb.trans hbu)
    (subcube (g^(k+2)) (g^(k+1))) (subcube_nonempty _ _) g hg
  have hb' : blockKill (g^(k+2)) (k-1) (subcube (g^(k+2)) (g^(k+1))) 1 -
      blockKill (g^(k+2)) k (subcube (g^(k+2)) (g^(k+1))) g ≤ e g := by linarith
  have hm := mul_le_mul_of_nonneg_left hb' (pow_nonneg (Nat.cast_nonneg (α := ℝ) g) (k-1))
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_inv_eq_mul] at he'
  nlinarith

end RandomKSAT

end

end OAI
