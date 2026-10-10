import OAI.Probability.SLE.ExponentialMartingales

namespace OAI

/-! Uniform second moments of terminal tests also control every smaller
nonnegative test, including tests evaluated at random times. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SLEExactGauge

lemma memLp_two_of_nonnegative_square_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    (M : ℝ≥0∞) (hM : M < ∞)
    (hb : (∫⁻ ω, ENNReal.ofReal (X ω)^2 ∂P) ≤ M) :
    MemLp X 2 P ∧ (∫ ω, X ω^2 ∂P) ≤ M.toReal := by
  have hi : Integrable (fun ω => X ω^2) P := by
    refine ⟨(hm.pow_const 2).aestronglyMeasurable,?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => sq_nonneg (X ω)))).mpr
    simpa only [ENNReal.ofReal_pow (hX _)] using hb.trans_lt hM
  have hmem := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi
  refine ⟨hmem,?_⟩
  have he : ENNReal.ofReal (∫ ω, X ω^2 ∂P) ≤ M := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω => sq_nonneg (X ω)))]
    simpa only [ENNReal.ofReal_pow (hX _)] using hb
  have ht := ENNReal.toReal_mono hM.ne he
  rwa [ENNReal.toReal_ofReal (integral_nonneg (fun ω => sq_nonneg (X ω)))] at ht

theorem integral_tendsto_of_nonnegative_L2_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X Z : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hXZ : ∀ n ω, X n ω ≤ Z n ω) (hZ : ∀ n, MemLp (Z n) 2 P)
    (A : ℝ) (hA : ∀ n, (∫ ω, Z n ω^2 ∂P) ≤ A)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y P ∧
      Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, Y ω ∂P)) := by
  have hX (n : ℕ) : MemLp (X n) 2 P :=
    (hZ n).mono' (hXm n).aestronglyMeasurable
      (ae_of_all _ (fun ω => by simpa only [Real.norm_of_nonneg (hX0 n ω)] using hXZ n ω))
  have hsq (n : ℕ) : (∫ ω, X n ω^2 ∂P) ≤ A := by
    apply (integral_mono (hX n).integrable_sq (hZ n).integrable_sq ?_).trans (hA n)
    intro ω
    exact pow_le_pow_left₀ (hX0 n ω) (hXZ n ω) 2
  obtain ⟨hY,hL1⟩ := finite_L1_tendsto_of_square_bound hX A hsq hlim
  exact ⟨hY,tendsto_integral_of_L1' Y
    (Eventually.of_forall (fun n => (hX n).integrable (by norm_num))) hL1⟩

end SLEExactGauge

end

end OAI
