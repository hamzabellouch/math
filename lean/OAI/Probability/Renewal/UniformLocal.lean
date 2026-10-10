import OAI.Probability.Renewal.LocalInversion
import OAI.Probability.Renewal.Envelope

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma sigma_polynomial_bound {a u σ V : ℝ} (ha : 0 < a ∧ a < 1) (hu : 0 < u)
    (hσ : 0 < σ) (hV : 0 < V) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 / a ≤ n)
    (hku : 1 ≤ (k : ℝ) * u ^ a) (hvar : σ ^ 2 ≤ (k : ℝ) * V * u ^ (a - 2)) :
    σ ≤ max V 1 * (k : ℝ) ^ n := by
  have hh := sigma_rpow_bound ha hu hσ hV hku hvar
  have hH : 0 < max V 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have heq (x : ℝ) (hx : 0 ≤ x) : (x ^ a) ^ (1 / a) = x := by
    rw [← Real.rpow_mul hx, mul_one_div_cancel ha.1.ne', Real.rpow_one]
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hσ.le a) hh (one_div_nonneg.mpr ha.1.le)
  rw [heq σ hσ.le, Real.mul_rpow (Real.rpow_pos_of_pos hH a).le hk0, heq _ hH.le] at hr
  refine hr.trans (mul_le_mul_of_nonneg_left ?_ hH.le)
  exact (Real.rpow_le_rpow_of_exponent_le hk1 hn).trans_eq (Real.rpow_natCast _ _)

namespace MomentData
variable {p : PMF ℕ} {a : ℝ} (M : MomentData p a)

lemma third_ratio_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ u (hu : 0 < u), u ≤ M.epsilon → ∀ k : ℕ, L ≤ (k : ℝ) * u ^ a →
      ∀ σ : ℝ, 0 < σ → σ ^ 2 = k * natVariance (tilt p u hu.le) →
        (k : ℝ) * natThird (tilt p u hu.le) / σ ^ 3 ≤ δ := by
  let B := M.thirdUpper / (M.varLower * δ)
  have hB : 0 < B := div_pos M.thirdUpper_pos (mul_pos M.varLower_pos hδ)
  let L := max 1 (B ^ 2 / M.varLower)
  refine ⟨L, le_max_left _ _, ?_⟩
  intro u hu hue k hku σ hσ hvar
  have hL : B ^ 2 / M.varLower ≤ (k : ℝ) * u ^ a := (le_max_right _ _).trans hku
  have hid2 : u ^ (a - 2) * u ^ 2 = u ^ a := by
    rw [Real.rpow_sub hu, Real.rpow_two]
    field_simp
  have hv := mul_le_mul_of_nonneg_left (M.var_lower u hu hue) (Nat.cast_nonneg k)
  rw [← hvar] at hv
  have hsu2 : M.varLower * ((k : ℝ) * u ^ a) ≤ (σ * u) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hv (sq_nonneg u)
    simpa only [mul_assoc, hid2, mul_pow, mul_left_comm M.varLower (k : ℝ)] using hh
  have hB2 : B ^ 2 ≤ M.varLower * ((k : ℝ) * u ^ a) := by
    have hh := (div_le_iff₀ M.varLower_pos).mp hL
    nlinarith
  have hBsu : B ≤ σ * u := by nlinarith [mul_pos hσ hu]
  have hid3 : u ^ (a - 3) * u = u ^ (a - 2) := by
    calc
      _ = u ^ (a - 3) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ (a - 3 + 1) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  have hth := mul_le_mul_of_nonneg_right (M.third_upper u hu hue) (by positivity : 0 ≤ (k : ℝ) * u)
  have hth' : ((k : ℝ) * natThird (tilt p u hu.le)) * u ≤ M.thirdUpper * ((k : ℝ) * u ^ (a - 2)) := by
    have hidR : M.thirdUpper * u ^ (a - 3) * ((k : ℝ) * u) =
        M.thirdUpper * ((k : ℝ) * u ^ (a - 2)) := by rw [← hid3]; ring
    rw [hidR] at hth
    nlinarith
  have hv' := mul_le_mul_of_nonneg_left hv (div_nonneg M.thirdUpper_pos.le M.varLower_pos.le)
  have hv'' : M.thirdUpper * ((k : ℝ) * u ^ (a - 2)) ≤ (M.thirdUpper / M.varLower) * σ ^ 2 := by
    have hidV : (M.thirdUpper / M.varLower) * ((k : ℝ) * (M.varLower * u ^ (a - 2))) =
        M.thirdUpper * ((k : ℝ) * u ^ (a - 2)) := by field_simp [M.varLower_pos.ne']
    rwa [hidV] at hv'
  have hT : M.thirdUpper / M.varLower ≤ δ * (σ * u) := by
    have hh := mul_le_mul_of_nonneg_left hBsu hδ.le
    have hid : δ * B = M.thirdUpper / M.varLower := by dsimp [B]; field_simp
    rwa [hid] at hh
  have herr := hth'.trans hv''
  have hlast := mul_le_mul_of_nonneg_right hT (sq_nonneg σ)
  apply (div_le_iff₀ (by positivity : 0 < σ ^ 3)).mpr
  nlinarith [mul_pos hσ hu]

lemma variance_ge_const (ha : a < 1) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hue : u ≤ M.epsilon) :
    M.varLower ≤ natVariance (tilt p u hu.le) := by
  have hp : 1 ≤ u ^ (a - 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
  have hm := mul_le_mul_of_nonneg_left hp M.varLower_pos.le
  simpa only [mul_one] using hm.trans (M.var_lower u hu hue)

end MomentData

lemma uniform_tilted_local (p : PMF ℕ) (hspan : SpanOne p) {a : ℝ} (ha : 0 < a ∧ a < 1)
    (hpower : BoundedPowerInput p a) :
    ∃ ω : ℝ, 1 ≤ ω ∧ ∃ L : ℝ, 1 ≤ L ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ u (hu : 0 < u), u ≤ ε → ∀ k : ℕ, N ≤ k → L ≤ (k : ℝ) * u ^ a →
        ∀ m : ℕ, let σ := Real.sqrt ((k : ℝ) * natVariance (tilt p u hu.le))
          |((m : ℝ) - k * natMean (tilt p u hu.le)) / σ| * ω ≤ 1 →
          Real.exp (-1) / (8 * Real.pi * σ) ≤ (sumLaw (tilt p u hu.le) k m).toReal := by
  obtain ⟨D⟩ := annulusData_exists p ha hpower
  obtain ⟨M⟩ := momentData_exists p ha hpower
  obtain ⟨ρ, hρ, εg, hεg, hgap⟩ := tilt_spectral_gap p hspan ha.1 hpower D.epsilon_pos
  obtain ⟨ω, hω, htail⟩ := exists_integral_tail_small (D.envelope_integrable M ha.1)
    (by positivity : 0 < Real.exp (-1) / 4)
  have hω0 : 0 < ω := zero_lt_one.trans_le hω
  let δ := Real.exp (-1) / (8 * ω ^ 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L, hL, hratio⟩ := M.third_ratio_small hδ
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / a)
  let H := max M.varUpper 1
  have hpoly : Tendsto (fun k : ℕ => 2 * Real.pi * H * ((k : ℝ) ^ n * ρ ^ k)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one n hρ.1 hρ.2).const_mul (2 * Real.pi * H)
  have hhigh := hpoly.eventually (Iio_mem_nhds (by positivity : 0 < Real.exp (-1) / 4))
  have hcast := (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
  have hlarge : ∀ᶠ k : ℕ in atTop,
      1 ≤ k ∧ ω ^ 2 ≤ 2 * (k : ℝ) ∧ (ω / Real.pi) ^ 2 ≤ (k : ℝ) * M.varLower ∧
        4 * ω ^ 5 / Real.exp (-1) ≤ (k : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hcast.eventually_ge_atTop (ω ^ 2 / 2),
      hcast.eventually_ge_atTop ((ω / Real.pi) ^ 2 / M.varLower),
      hcast.eventually_ge_atTop (4 * ω ^ 5 / Real.exp (-1))] with k hk h2 hv he
    exact ⟨hk, by linarith, (div_le_iff₀ M.varLower_pos).mp hv, he⟩
  obtain ⟨N, hN⟩ := (hlarge.and hhigh).exists_forall_of_atTop
  let ε := min D.epsilon (min M.epsilon (min εg 1))
  refine ⟨ω, hω, L, hL, ε, lt_min D.epsilon_pos (lt_min M.epsilon_pos (lt_min hεg zero_lt_one)), N, ?_⟩
  intro u hu hue k hk hku m σ hcenter
  have hdeps : u ≤ D.epsilon ∧ u ≤ M.epsilon ∧ u ≤ εg ∧ u ≤ 1 := by
    simpa only [ε, le_min_iff] using hue
  obtain ⟨⟨hk1, hk2, hkv, hke⟩, hkhigh⟩ := hN k hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hv0 := M.variance_ge_const ha.2 hu hdeps.2.2.2 hdeps.2.1
  have hvpos : 0 < natVariance (tilt p u hu.le) := M.varLower_pos.trans_le hv0
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos hkpos' hvpos)
  have hvar : σ ^ 2 = k * natVariance (tilt p u hu.le) := Real.sq_sqrt (mul_pos hkpos' hvpos).le
  have hwidth : ω ≤ Real.pi * σ := by
    have hh := mul_le_mul_of_nonneg_left hv0 hkpos'.le
    rw [← hvar] at hh
    have hsq : (ω / Real.pi) ^ 2 ≤ σ ^ 2 := hkv.trans hh
    have hdiv : ω / Real.pi ≤ σ := by nlinarith [sq_nonneg σ]
    exact (div_le_iff₀ Real.pi_pos).mp hdiv |>.trans_eq (mul_comm _ _)
  have hσup : σ ≤ H * (k : ℝ) ^ n := by
    apply sigma_polynomial_bound ha hu hσ M.varUpper_pos hk1 hn (hL.trans hku)
    rw [hvar]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (M.var_upper u hu hdeps.2.1) hkpos'.le
  apply local_lower_of_envelope (tilt p u hu.le) (tilt_moment_integrable p hu 3)
    hkpos m hσ hω hvar hk2 hwidth hcenter (D.envelope_integrable M ha.1)
    (D.envelope_nonneg M) (pow_nonneg hρ.1 k)
  · intro t ht
    apply D.normalized_bound M ha hu hdeps.1 hdeps.2.1 (hL.trans hku) hσ hvar hρ.1
      (hgap u hu.le hdeps.2.2.1)
    exact abs_le.mpr ⟨by simpa [neg_mul] using ht.1, ht.2⟩
  · exact htail
  · have hm := mul_le_mul_of_nonneg_right hσup (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (pow_nonneg hρ.1 k))
    nlinarith
  · have hr := hratio u hu hdeps.2.1 k hku σ hσ hvar
    have hfirst : (k : ℝ) * natThird (tilt p u hu.le) / σ ^ 3 * ω ^ 4 ≤ Real.exp (-1) / 8 := by
      have hh := mul_le_mul_of_nonneg_right hr (pow_nonneg hω0.le 4)
      have hid : δ * ω ^ 4 = Real.exp (-1) / 8 := by dsimp [δ]; field_simp
      simpa only [hid] using hh
    have hsecond : ω ^ 5 / (2 * (k : ℝ)) ≤ Real.exp (-1) / 8 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := (div_le_iff₀ (Real.exp_pos (-1))).mp hke
      nlinarith
    have hid : 2 * ω * ((k * natThird (tilt p u hu.le) / σ ^ 3) * ω ^ 3 / 2 + ω ^ 4 / (4 * k)) =
        (k * natThird (tilt p u hu.le) / σ ^ 3) * ω ^ 4 + ω ^ 5 / (2 * k) := by ring
    rw [hid]
    linarith

end HoneycombLocal

end

end OAI
