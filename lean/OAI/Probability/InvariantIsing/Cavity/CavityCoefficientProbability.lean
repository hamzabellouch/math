import OAI.Probability.InvariantIsing.Cavity.CavityUniformMomentConstants

namespace OAI

/-! A bounded continuous test detects deviations of the three cavity
coefficients. Weak convergence to deterministic coefficients therefore
gives the probability estimate required by the replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFactorDeviation {d n : ℕ} (A B : CavityFactorBlocks d n) : ℝ :=
  cavityFactorSize (A.1-B.1) (A.2.1-B.2.1) (A.2.2-B.2.2)

lemma continuous_cavityFactorDeviation {d n : ℕ} (B : CavityFactorBlocks d n) :
    Continuous (fun A => cavityFactorDeviation A B) := by
  unfold cavityFactorDeviation cavityFactorSize
  have hK : Continuous (fun A : CavityFactorBlocks d n => A.1 - B.1) :=
    continuous_fst.sub continuous_const
  have hL : Continuous (fun A : CavityFactorBlocks d n => A.2.1 - B.2.1) :=
    (continuous_fst.comp continuous_snd).sub continuous_const
  have hC : Continuous (fun A : CavityFactorBlocks d n => A.2.2 - B.2.2) :=
    (continuous_snd.comp continuous_snd).sub continuous_const
  exact (((continuous_cavityMatrixMass d d).comp hK).add
    ((continuous_cavityMatrixMass d n).comp hL)).add
      ((continuous_cavityMatrixMass n n).comp hC)

lemma cavityFactorDeviation_nonneg {d n : ℕ} (A B : CavityFactorBlocks d n) :
    0 ≤ cavityFactorDeviation A B := cavityFactorSize_nonneg _ _ _

@[simp] lemma cavityFactorDeviation_self {d n : ℕ} (A : CavityFactorBlocks d n) :
    cavityFactorDeviation A A = 0 := by
  simp [cavityFactorDeviation, cavityFactorSize, cavityMatrixMass]

def cavityFactorDeviationTest {d n : ℕ} (A₀ : CavityFactorBlocks d n)
    (δ : ℝ) (hδ : 0 < δ) : CavityFactorBlocks d n →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun A => min 1 (cavityFactorDeviation A A₀ / δ))
    (continuous_const.min ((continuous_cavityFactorDeviation A₀).div_const δ)) 1
    (fun A => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (le_min (by norm_num) (div_nonneg (cavityFactorDeviation_nonneg A A₀) hδ.le))]
      exact min_le_left _ _)

theorem cavity_factor_coefficients_probability {d n : ℕ}
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : (k : ℕ) → Ω k → CavityFactorBlocks d n) (hA : ∀ k, Measurable (A k))
    (A₀ : CavityFactorBlocks d n)
    (hlim : ∀ F : CavityFactorBlocks d n →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, F (A k ω) ∂P k) atTop (𝓝 (F A₀)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => (P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀})
      atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d n) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin n → ℝ) × (Fin n → Fin n → ℝ))))
  let F := cavityFactorDeviationTest A₀ δ hδ
  have hm k : Measurable (fun ω => cavityFactorDeviation (A k ω) A₀) :=
    (continuous_cavityFactorDeviation A₀).measurable.comp (hA k)
  have hs k : MeasurableSet {ω : Ω k | δ < cavityFactorDeviation (A k ω) A₀} :=
    measurableSet_lt measurable_const (hm k)
  have hF k : Integrable (fun ω => F (A k ω)) (P k) :=
    Integrable.of_bound (F.continuous.measurable.comp (hA k)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        change ‖min 1 (cavityFactorDeviation (A k ω) A₀ / δ)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg
          (le_min (by norm_num) (div_nonneg (cavityFactorDeviation_nonneg _ _) hδ.le))]
        exact min_le_left _ _)
  have hb k : (P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀} ≤
      ∫ ω, F (A k ω) ∂P k := by
    rw [← integral_indicator_one (hs k)]
    apply integral_mono ((integrable_const (1 : ℝ)).indicator (hs k)) (hF k)
    intro ω
    by_cases h : δ < cavityFactorDeviation (A k ω) A₀
    · rw [indicator_of_mem (show ω ∈ {ω | δ < cavityFactorDeviation (A k ω) A₀} from h)]
      change 1 ≤ min 1 (cavityFactorDeviation (A k ω) A₀ / δ)
      exact le_min le_rfl ((le_div_iff₀ hδ).mpr (by simpa using h.le))
    · rw [indicator_of_notMem (show ω ∉ {ω | δ < cavityFactorDeviation (A k ω) A₀} from h)]
      exact le_min (by norm_num) (div_nonneg (cavityFactorDeviation_nonneg _ _) hδ.le)
  apply squeeze_zero (fun k => measureReal_nonneg) hb
  simpa only [F, cavityFactorDeviationTest, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    cavityFactorDeviation_self, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hlim F

end InvariantIsing

end

end OAI
