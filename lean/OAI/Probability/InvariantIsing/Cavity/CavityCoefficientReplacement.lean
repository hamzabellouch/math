import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientProbability
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientMean

namespace OAI

/-! Convergence in probability of the actual cavity coefficients suffices
for their replacement in every capped replica moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_capped_coefficient_probability_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] {d k r : ℕ}
    (A A' : (n : ℕ) → Ω n → CavityFactorBlocks d k)
    (hA : ∀ n, Measurable (A n)) (hA' : ∀ n, Measurable (A' n))
    (y : (n : ℕ) → Ω n → Fin r → EuclideanSpace ℝ (Fin d)) (hy : ∀ n, Measurable (y n))
    (ε : (n : ℕ) → Ω n → Fin r → Spin k) (hε : ∀ n, Measurable (ε n))
    (F : (n : ℕ) → Ω n → ℝ) (hF : ∀ n, Measurable (F n))
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ n ω, |F n ω| ≤ B)
    (T : ℝ)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) (A' n ω)}) atTop (𝓝 0))
    (hi : ∀ n, Integrable (fun ω => ∑ i, (1 + ‖y n ω i‖^2)) (P n))
    {M : ℝ} (hM : ∀ n, (∫ ω, ∑ i, (1 + ‖y n ω i‖^2) ∂P n) ≤ M) :
    Tendsto (fun n =>
      (∫ ω, cavityCappedReplicaProduct (A n ω) T (y n ω) (ε n ω) * F n ω ∂P n) -
      ∫ ω, cavityCappedReplicaProduct (A' n ω) T (y n ω) (ε n ω) * F n ω ∂P n)
      atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d k) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin k → ℝ) × (Fin k → Fin k → ℝ))))
  let : MeasurableSub₂ (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (MeasurableSub₂ (Fin d → Fin d → ℝ))
  let : MeasurableSub₂ (Matrix (Fin d) (Fin k) ℝ) :=
    inferInstanceAs (MeasurableSub₂ (Fin d → Fin k → ℝ))
  let : MeasurableSub₂ (Matrix (Fin k) (Fin k) ℝ) :=
    inferInstanceAs (MeasurableSub₂ (Fin k → Fin k → ℝ))
  let E := Real.exp ((r : ℝ) * T) * B
  have hE : 0 ≤ E := mul_nonneg (Real.exp_pos _).le hB
  have hM0 : 0 ≤ M := (integral_nonneg (fun ω =>
    Finset.sum_nonneg (fun _ _ => by positivity))).trans (hM 0)
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ := η / (2 * (E*M+1))
  have hden : 0 < 2 * (E*M+1) := by positivity
  have hδ : 0 < δ := div_pos hη hden
  have hδeq : 2 * (E*M+1) * δ = η := by
    dsimp only [δ]
    field_simp
  have hsmall : E * δ * M < η/2 := by nlinarith
  let s := fun n => {ω : Ω n | cavityFactorDeviation (A n ω) (A' n ω) ≤ δ}
  have hs n : MeasurableSet (s n) := by
    have hdev : Measurable (fun ω => cavityFactorDeviation (A n ω) (A' n ω)) := by
      unfold cavityFactorDeviation cavityFactorSize
      exact ((((continuous_cavityMatrixMass d d).measurable.comp
        ((hA n).fst.sub (hA' n).fst)).add
        ((continuous_cavityMatrixMass d k).measurable.comp
          ((hA n).snd.fst.sub (hA' n).snd.fst))).add
        ((continuous_cavityMatrixMass k k).measurable.comp
          ((hA n).snd.snd.sub (hA' n).snd.snd)))
    exact measurableSet_le hdev measurable_const
  have hbad : Tendsto (fun n => (P n).real (s n)ᶜ) atTop (𝓝 0) := by
    simpa only [s, Set.compl_ofPred, not_le] using hprob δ hδ
  have ht : Tendsto (fun n => 2*E * (P n).real (s n)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbad.const_mul (2*E)
  have htail := ht.eventually (gt_mem_nhds (show (0 : ℝ) < η/2 by positivity))
  filter_upwards [htail] with n hn
  have hb := cavity_capped_coefficient_mean_error (P n) (A n) (A' n) (hA n) (hA' n)
    (y n) (hy n) (ε n) (hε n) (F n) (hF n) hB (hFb n) T (s n) (hs n) hδ.le
    (fun ω hω => hω) (hi n) (hM n)
  rw [Real.dist_eq, sub_zero]
  apply hb.trans_lt
  change E * (δ * M + 2 * (P n).real (s n)ᶜ) < η
  nlinarith

end InvariantIsing

end

end OAI
