import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CappedBilinearConvergence
import OAI.Analysis.RieszRectifiability.Limits.CappedWeakConvergence
import OAI.Analysis.RieszRectifiability.Limits.LimitEnergyDuality

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem fractionalEnergy_integrable_of_capped_bounds {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (v : Ambient d → ℝ)
    (hv : Measurable v) (hvL2 : MemLp v 2 μ) (E : ℝ)
    (hcap : ∀ ε : ℝ, 0 < ε → (∫ q, cappedPairEnergy m ε v q ∂μ.prod μ) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m v q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy m v q.1 q.2 ∂μ.prod μ) ≤ E := by
  apply fractionalEnergy_integrable_of_uniform_bound μ m v hv hvL2 E
  intro ε hε
  have hs : MeasurableSet {q : Ambient d × Ambient d | ε < dist q.1 q.2} :=
    measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable
  have heq : (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
      fractionalPairEnergy m v q.1 q.2 ∂μ.prod μ) =
      ∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2}, cappedPairEnergy m ε v q ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hs] with q hq
    rw [cappedPairEnergy, cappedInverseDistancePow_eq _ _ _ hq.le]
    rfl
  rw [heq]
  exact (setIntegral_le_integral (cappedPairEnergy_integrable m ε hε μ v hvL2)
    (Filter.Eventually.of_forall fun q =>
      mul_nonneg (sq_nonneg _) (cappedInverseDistancePow_nonneg (m + 1) ε q))).trans (hcap ε hε)

theorem limiting_fractional_energy_bound {d : ℕ} (m : ℕ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (hv : MemLp v 2 (ν : Measure (Ambient d))) (hvm : Measurable v)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (hM : 0 ≤ M) (htotal : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M)
    (hsecond : ∀ᶠ j in atTop, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ M)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 (ν : Measure (Ambient d)) → (∀ j, MemLp ψ 2 (μ j : Measure (Ambient d))) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, v x * ψ x ∂(ν : Measure (Ambient d)))))
    (henergy : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (E : ℝ) (hE : ∀ j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy m (w j) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m v q.1 q.2)
      ((ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy m v q.1 q.2
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ≤ E := by
  have hE0 : 0 ≤ E := (integral_nonneg fun q => fractionalPairEnergy_nonneg m (w 0) q.1 q.2).trans (hE 0)
  apply fractionalEnergy_integrable_of_capped_bounds m (ν : Measure (Ambient d)) v hvm hv E
  intro ε hε
  apply capped_energy_bound_from_lipschitz_tests m ε hε (ν : Measure (Ambient d)) v hv E hE0
  intro g K B hg hB _
  have hleft := capped_bilinear_tendsto (fun j => (μ j : Measure (Ambient d))) (ν : Measure (Ambient d))
    w v hw hv ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M hM htotal hsecond
    hmoment m ε hε g K B hg hB
  have hright := capped_energy_tendsto_of_weak μ ν hweak ι s hs hd hcover hcoverν z r hr hrzero
    hcell hcellν hmass M hM htotal m ε hε g K B hg hB
  apply le_of_tendsto_of_tendsto (hleft.pow 2) (hright.const_mul E)
  apply Filter.Eventually.of_forall
  intro j
  have hgL2 : MemLp g 2 (μ j : Measure (Ambient d)) :=
    MemLp.of_bound hg.continuous.measurable.aestronglyMeasurable (B : ℝ)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  exact capped_bilinear_variational_bound m ε hε (μ j : Measure (Ambient d)) (w j) g
    (hw j) hgL2 (henergy j) E (hE j)

end

end RieszRectifiability

end OAI
