import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedReweighting

namespace OAI

/-! A uniform second moment of the negative log normalizer permits
removing the positive floor after the finite-replica limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_floor_bound {z δ M R : ℝ} (hz : 0 < z) (hzM : z ≤ M)
    (_hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) :
    0 ≤ Real.log (z + δ) - Real.log z ∧
      Real.log (z + δ) - Real.log z ≤
        δ * Real.exp R + (1 + Real.log (M + 1)) * (max (-Real.log z) 0) ^ 2 / R := by
  have hzδ : 0 < z + δ := add_pos_of_pos_of_nonneg hz hδ
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hL : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith [_hM])
  refine ⟨sub_nonneg.mpr (Real.log_le_log hz (by linarith)), ?_⟩
  have hsec : Real.log (z + δ) - Real.log z ≤ δ / z := by
    rw [← Real.log_div hzδ.ne' hz.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos hzδ hz)).trans_eq
    field_simp
    ring
  by_cases hsmall : -Real.log z ≤ R
  · have hzr : Real.exp (-R) ≤ z := by
      conv_rhs => rw [← Real.exp_log hz]
      exact Real.exp_le_exp.mpr (by linarith)
    have hd : δ / z ≤ δ * Real.exp R := by
      have hh := div_le_div_of_nonneg_left hδ (Real.exp_pos (-R)) hzr
      simpa only [div_eq_mul_inv, Real.exp_neg, inv_inv] using hh
    exact (hsec.trans hd).trans (le_add_of_nonneg_right (by positivity))
  · have hy : max (-Real.log z) 0 = -Real.log z := max_eq_left (by linarith)
    rw [hy]
    have hY : -Real.log z ≤ (-Real.log z) ^ 2 / R := by
      apply (le_div_iff₀ hR0).mpr
      nlinarith
    have h1 : 1 ≤ (-Real.log z) ^ 2 / R := (by linarith : 1 ≤ -Real.log z).trans hY
    have hu : Real.log (z + δ) - Real.log z ≤ Real.log (M + 1) + -Real.log z := by
      have hh := Real.log_le_log hzδ (show z + δ ≤ M + 1 by linarith)
      linarith
    calc
      _ ≤ Real.log (M + 1) + -Real.log z := hu
      _ ≤ Real.log (M + 1) * ((-Real.log z) ^ 2 / R) + ((-Real.log z) ^ 2 / R) :=
        add_le_add (by nlinarith) hY
      _ = (1 + Real.log (M + 1)) * (-Real.log z) ^ 2 / R := by ring
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hδ (Real.exp_pos R).le)

lemma cavity_log_floor_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M K δ R : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P)
    (hK : (∫ ω, (max (-Real.log (Z ω)) 0)^2 ∂P) ≤ K) :
    0 ≤ (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) ∧
      (∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P) ≤
        δ * Real.exp R + (1 + Real.log (M + 1)) * K / R := by
  let L := 1 + Real.log (M + 1)
  have hL : 0 ≤ L := by dsimp only [L]; have := Real.log_nonneg (show 1 ≤ M + 1 by linarith); linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hbound ω := cavity_log_floor_bound (hZ0 ω) (hZM ω) hM hδ hδ1 hR
  have him : Integrable (fun ω => δ * Real.exp R + L * (max (-Real.log (Z ω)) 0)^2 / R) P :=
    (integrable_const _).add ((hi.const_mul L).div_const R)
  have hie : Integrable (fun ω => Real.log (Z ω + δ) - Real.log (Z ω)) P :=
    him.mono' ((hZ.add_const δ).log.sub hZ.log).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1]
        exact (hbound ω).2)
  refine ⟨integral_nonneg (fun ω => (hbound ω).1), ?_⟩
  calc
    _ ≤ ∫ ω, δ * Real.exp R + L * (max (-Real.log (Z ω)) 0)^2 / R ∂P :=
      integral_mono hie him (fun ω => (hbound ω).2)
    _ = δ * Real.exp R + L * (∫ ω, (max (-Real.log (Z ω)) 0)^2 ∂P) / R := by
      rw [integral_add (integrable_const _) ((hi.const_mul L).div_const R)]
      simp only [integral_div, integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK hL) hR0.le)

lemma cavity_log_floor_uniform {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : (n : ℕ) → Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {M K : ℝ} (hZ0 : ∀ n ω, 0 < Z n ω) (hZM : ∀ n ω, Z n ω ≤ M)
    (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hi : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hK : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ ∈ Icc (0 : ℝ) δ₀, ∀ n,
      0 ≤ (∫ ω, Real.log (Z n ω + δ) - Real.log (Z n ω) ∂P n) ∧
        (∫ ω, Real.log (Z n ω + δ) - Real.log (Z n ω) ∂P n) < ε := by
  intro ε hε
  let L := 1 + Real.log (M + 1)
  have hL : 0 ≤ L := by dsimp only [L]; have := Real.log_nonneg (show 1 ≤ M + 1 by linarith); linarith
  let R := 1 + 4 * L * K / ε
  have hR : 1 ≤ R := le_add_of_nonneg_right (div_nonneg (by positivity) hε.le)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRmul : R * ε = ε + 4 * L * K := by
    dsimp only [R]
    field_simp
  have htail : L * K / R < ε / 4 := by
    apply (div_lt_iff₀ hR0).mpr
    nlinarith
  refine ⟨min 1 (ε / (4 * Real.exp R)), lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro δ hδ n
  have hδ1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have hδe : δ * Real.exp R ≤ ε / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * Real.exp R by positivity)).mp
      (hδ.2.trans (min_le_right _ _))
    nlinarith
  have hh := cavity_log_floor_integral_bound (P n) (Z n) (hZ n) (hZ0 n) (hZM n)
    hM hδ.1 hδ1 hR (hi n) (hK n)
  refine ⟨hh.1, hh.2.trans_lt ?_⟩
  change δ * Real.exp R + L * K / R < ε
  linarith

end InvariantIsing

end

end OAI
