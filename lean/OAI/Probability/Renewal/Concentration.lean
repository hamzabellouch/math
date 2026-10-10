import OAI.Probability.Renewal.LocalInversion
import OAI.Probability.Renewal.Envelope

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma AnnulusData.original_normalized {p : PMF ℕ} {a : ℝ} (D : AnnulusData p a)
    (ha : 0 < a) {k : ℕ} (hk : 0 < k) {s : ℝ} (hs : 0 < s) (hsa : s ^ a = k)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hgap : ∀ t : ℝ, D.epsilon ≤ |t| → |t| ≤ Real.pi → ‖latticeChar p t‖ ≤ ρ)
    (t : ℝ) (ht : |t| ≤ Real.pi * s) :
    ‖latticeChar p (t / s)‖ ^ k ≤ Real.exp (-D.decayConst * |t| ^ a) + ρ ^ k := by
  have hθ : |t / s| ≤ Real.pi := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact ht
  by_cases hlo : |t / s| ≤ D.epsilon
  · have hb := pow_le_pow_left₀ (norm_nonneg _) (D.original_small ha hlo) k
    rw [← Real.exp_nat_mul, abs_div, abs_of_pos hs,
      Real.div_rpow (abs_nonneg t) hs.le, hsa] at hb
    have hid : (k : ℝ) * (-D.decayConst * (|t| ^ a / (k : ℝ))) = -D.decayConst * |t| ^ a := by
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
    rw [hid] at hb
    exact hb.trans (le_add_of_nonneg_right (pow_nonneg hρ k))
  · have hb := pow_le_pow_left₀ (norm_nonneg _) (hgap (t / s) (le_of_not_ge hlo) hθ) k
    exact hb.trans (le_add_of_nonneg_left (Real.exp_pos _).le)

lemma lattice_mass_upper_of_envelope (p : PMF ℕ) (k m : ℕ) {s : ℝ} (hs : 0 < s)
    {g : ℝ → ℝ} (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) {η : ℝ} (_hη : 0 ≤ η)
    (hbound : ∀ t ∈ Icc (-Real.pi * s) (Real.pi * s),
      ‖latticeChar p (t / s)‖ ^ k ≤ g t + η) :
    2 * Real.pi * s * (sumLaw p k m).toReal ≤ (∫ t : ℝ, g t) + 2 * Real.pi * s * η := by
  have hR : 0 ≤ Real.pi * s := by positivity
  have hfi := (continuous_localIntegrand p k m s).integrableOn_Icc (μ := volume) (a := -Real.pi * s) (b := Real.pi * s)
  calc
    _ = ‖∫ t : ℝ in Icc (-Real.pi * s) (Real.pi * s), localIntegrand p k m s t‖ := by
      rw [scaled_inversion p k m hs, norm_mul]
      norm_num [norm_mul, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos Real.pi_pos,
        abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∫ t : ℝ in Icc (-Real.pi * s) (Real.pi * s), ‖localIntegrand p k m s t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Icc (-Real.pi * s) (Real.pi * s), g t + η := by
      apply setIntegral_mono_on hfi.norm (hg.integrableOn.add (integrable_const _)) measurableSet_Icc
      intro t ht
      rw [norm_localIntegrand]
      exact hbound t ht
    _ = (∫ t : ℝ in Icc (-Real.pi * s) (Real.pi * s), g t) + 2 * Real.pi * s * η := by
      rw [integral_add hg.integrableOn (integrable_const _)]
      simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, Real.volume_real_Icc]
      rw [max_eq_left (by nlinarith : 0 ≤ Real.pi * s - -Real.pi * s)]
      ring
    _ ≤ _ := add_le_add (setIntegral_le_integral hg (ae_of_all _ hg0)) le_rfl

theorem local_concentration (p : PMF ℕ) (hspan : SpanOne p) {a : ℝ}
    (ha : 0 < a ∧ a < 1) (hpower : BoundedPowerInput p a) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ,
      (sumLaw p k m).toReal ≤ C * (k : ℝ) ^ (-1 / a) := by
  obtain ⟨D⟩ := annulusData_exists p ha hpower
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ := lattice_spectral_gap p hspan D.epsilon_pos
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / a)
  obtain ⟨T, hT⟩ := (tendsto_pow_const_mul_const_pow_of_lt_one n hρ0 hρ1).bddAbove_range
  let g := fun t : ℝ => Real.exp (-D.decayConst * |t| ^ a)
  have hgi : Integrable g := integrable_stretched_exp ha.1 D.decayConst_pos
  have hg0 : ∀ t, 0 ≤ g t := fun t => (Real.exp_pos _).le
  let I := ∫ t : ℝ, g t
  have hI : 0 ≤ I := integral_nonneg hg0
  let C := I / (2 * Real.pi) + max T 1
  have hC : 0 < C := by
    dsimp [C]
    have : (1 : ℝ) ≤ max T 1 := le_max_right _ _
    positivity
  refine ⟨C, hC, ?_⟩
  intro k hk m
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let s := (k : ℝ) ^ (1 / a)
  have hs : 0 < s := Real.rpow_pos_of_pos hk' _
  have hsa : s ^ a = (k : ℝ) := by
    dsimp [s]
    rw [← Real.rpow_mul hk'.le, div_mul_cancel₀ _ ha.1.ne', Real.rpow_one]
  have hsle : s ≤ (k : ℝ) ^ n := by
    exact (Real.rpow_le_rpow_of_exponent_le hk1 hn).trans_eq (Real.rpow_natCast _ _)
  have hT' : s * ρ ^ k ≤ max T 1 := by
    have hb : (k : ℝ) ^ n * ρ ^ k ≤ T := hT (mem_range_self k)
    exact ((mul_le_mul_of_nonneg_right hsle (pow_nonneg hρ0 k)).trans hb).trans (le_max_left _ _)
  have hbound := lattice_mass_upper_of_envelope p k m hs hgi hg0 (pow_nonneg hρ0 k) (by
    intro t ht
    exact D.original_normalized ha.1 hk0 hs hsa hρ0 hgap t (by apply abs_le.mpr; simpa only [← neg_mul, mem_Icc] using ht))
  have hconst : (∫ t : ℝ, g t) + 2 * Real.pi * s * ρ ^ k ≤ 2 * Real.pi * C := by
    have hh := mul_le_mul_of_nonneg_left hT' (by positivity : 0 ≤ 2 * Real.pi)
    dsimp [C, I]
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
    nlinarith [hh]
  have hfinal : (sumLaw p k m).toReal ≤ C / s := by
    apply (le_div_iff₀ hs).mpr
    have hh := hbound.trans hconst
    nlinarith [Real.pi_pos]
  have hp : (k : ℝ) ^ (-1 / a) = s⁻¹ := by
    rw [neg_div, Real.rpow_neg hk'.le]
  calc
    _ ≤ C / s := hfinal
    _ = C * (k : ℝ) ^ (-1 / a) := by rw [hp, div_eq_mul_inv]

theorem annular_mass_and_concentration (p : PMF ℕ) (_hp : p 0 = 0) (hspan : SpanOne p)
    {a : ℝ} (ha : 0 < a ∧ a < 1) (hpower : BoundedPowerInput p a) :
    ∃ M > (1 : ℝ), ∃ c₁ > (0 : ℝ), ∃ C₁ > (0 : ℝ),
      (∀ᶠ x : ℝ in atTop,
        c₁ * x ^ (-a) ≤ p.toMeasure.real {j | x / M < (j : ℝ) ∧ (j : ℝ) ≤ x}) ∧
      (∀ k : ℕ, 1 ≤ k → (⨆ j : ℕ, (sumLaw p k j).toReal) ≤ C₁ * (k : ℝ) ^ (-1 / a)) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 0 < t →
        (sumLaw p k).toMeasure.real {j | t < (j : ℝ)} ≤ C₁ * k * t ^ (-a)) := by
  obtain ⟨M, hM, c, hc, hann⟩ := annular_mass p ha hpower
  obtain ⟨C, hC, hconc⟩ := local_concentration p hspan ha hpower
  obtain ⟨D, hD, htail⟩ := sum_tail_power p ha hpower
  refine ⟨M, hM, c, hc, max C D, hC.trans_le (le_max_left _ _), hann, ?_, ?_⟩
  · intro k hk
    apply ciSup_le
    intro j
    exact (hconc k hk j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg k) _))
  · intro k hk t ht
    exact (htail k hk t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg k))
      (Real.rpow_nonneg ht.le _))

end HoneycombLocal

end

end OAI
