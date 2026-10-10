import OAI.Probability.FreeIsing.Conditioning.CovarianceLimit
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianPosterior
import OAI.Probability.FreeIsing.Stochastic.SelectedBrownianSufficiency

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianHistoryNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.condExp_finiteIsingBrownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (q : (D → IsingSpin) → ℝ) (t : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    ρ[fun p => q (D.restrict p.1) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i : D => fun s : Iic t =>
            (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance] =ᵐ[ρ]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta (v : D) => spinSign (eta v)) q
        (finiteIsingBrownianObservation B D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hq : Measurable (fun sigma : TreeVertex d → IsingSpin => q (D.restrict sigma)) :=
    (measurable_of_finite q).comp D.measurable_restrict
  have hqi : Integrable (fun sigma : TreeVertex d → IsingSpin => q (D.restrict sigma)) μ := by
    classical
    apply (integrable_const (∑ eta, |q eta|)).mono' hq.aestronglyMeasurable
    filter_upwards with sigma
    exact Finset.single_le_sum (fun eta _ => abs_nonneg (q eta))
      (Finset.mem_univ (D.restrict sigma))
  have hs : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      fun i : TreeVertex d => spinSign (sigma i)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_of_finite spinSign).comp (measurable_pi_apply (i : TreeVertex d))
  have h := TerminalSufficiency.condExp_planted_selected_past_eq_terminal
    μ ν hB hmB (fun i : D => (i : TreeVertex d)) Subtype.val_injective
    (fun sigma i => spinSign (sigma i))
    (fun sigma => q (D.restrict sigma)) hs hq hqi t
  dsimp only
  apply h.trans
  have hc := hμ.condExp_finiteIsingBrownian_observable ν hB hmB D hD t q
  unfold finiteIsingBrownianObservation at hc ⊢
  simpa only [Real.toNNReal_coe] using hc

theorem HasFreeIsingLaw.finiteIsingBrownianCovariance_eq_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v u : D) (t : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    finiteIsingBrownianCovariance beta D v u B t =ᵐ[ρ]
      posteriorCovariance ρ
        (MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i : D => fun s : Iic t =>
              (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i)) inferInstance)
        (fun p => spinSign (p.1 (v : TreeVertex d)))
        (fun p => spinSign (p.1 (u : TreeVertex d))) := by
  filter_upwards [hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
      (fun eta => spinSign (eta v) * spinSign (eta u)) t,
    hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
      (fun eta => spinSign (eta v)) t,
    hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
      (fun eta => spinSign (eta u)) t] with p hp hv hu
  exact congrArg₂ (fun a b : ℝ => a - b) hp.symm
    (congrArg₂ (· * ·) hv.symm hu.symm)

end Problem367

end

end OAI
