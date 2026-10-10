import OAI.Probability.FreeIsing.Energy.ActualCriticalFieldMoments
import OAI.Probability.FreeIsing.Stochastic.SelectedBrownianFieldLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem exists_brownianComponentField_critical_moment_tail
    {d : ℕ} (hd : 3 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {beta : ℝ} (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (μ : Measure (TreeVertex d → IsingSpin)),
      HasFreeIsingLaw (Real.tanh beta) μ →
      ∀ (ν : Measure Ω) (B : ℝ≥0 → Ω → ℝ), IsPreBrownianReal B ν →
      (∀ t, Measurable (B t)) →
      ∀ (t : ℝ≥0), 0 < t → (t : ℝ) ≤ 1 → ∀ c : Fin d,
      (∀ p : ℕ, Integrable
        (fun q => |selectedBrownianField μ ν B t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p)
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) ∧
      (∀ p : ℕ, (∫ q,
        |selectedBrownianField μ ν B t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ≤
        Real.exp (K * (p : ℝ) ^ 2) * (t : ℝ) ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / (t : ℝ)) →
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
          {q | (t : ℝ) ^ (1 / 8 : ℝ) <
            |selectedBrownianField μ ν B t (componentIndexVertex (c := c))
              (RootedBroadcast.branchRoot c) q|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / (t : ℝ)) ^ 2) / (512 * K)))) := by
  obtain ⟨K, hK, hGaussian⟩ :=
    exists_gaussianComponentField_critical_moment_tail hd hb hcritical
  refine ⟨K, hK, ?_⟩
  intro μ hμ ν B hB hmB t ht ht1 c
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hBound := hGaussian μ hμ t ht ht1 c
  have hLaw := selectedBrownianField_identDistrib_gaussian μ ν hB hmB t
    (componentIndexVertex (c := c)) (componentIndexVertex_injective c)
    (RootedBroadcast.branchRoot c)
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact (hLaw.comp (show Measurable (fun x : ℝ => |x| ^ p) by fun_prop)).integrable_iff.mpr
      (hBound.1 p)
  · intro p
    exact (selectedBrownianField_abs_moment_eq_gaussian μ ν hB hmB t _
      (componentIndexVertex_injective c) (RootedBroadcast.branchRoot c) p).trans_le
        (hBound.2.1 p)
  · intro hsmall
    rw [selectedBrownianField_tail_eq_gaussian μ ν hB hmB t _
      (componentIndexVertex_injective c)]
    exact hBound.2.2 hsmall

end Problem367

end

end OAI
