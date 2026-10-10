import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.VectorNormalizedEnergy
import OAI.Analysis.RieszRectifiability.Kernel.WeightedCentering

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem inner_fractional_energy_le_cutoff {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ]
    (s t : Set (Ambient d)) (hs : MeasurableSet s) (hst : s ⊆ t)
    (u χ : Ambient d → ℝ) (b δ : ℝ) (hone : ∀ x ∈ s, χ x = 1)
    (hE : Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy m (fun x => χ x * (u x - b) / δ) q.1 q.2)
      ((μ.restrict t).prod (μ.restrict t))) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy m (fun x => u x / δ) q.1 q.2)
      ((μ.restrict s).prod (μ.restrict s)) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy m (fun x => u x / δ) q.1 q.2
          ∂(μ.restrict s).prod (μ.restrict s)) ≤
      ∫ q : Ambient d × Ambient d,
        fractionalPairEnergy m (fun x => χ x * (u x - b) / δ) q.1 q.2
          ∂(μ.restrict t).prod (μ.restrict t) := by
  have hmeasure : (μ.restrict s).prod (μ.restrict s) ≤ (μ.restrict t).prod (μ.restrict t) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (Set.prod_mono hst hst) le_rfl
  have heq : (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy m (fun x => u x / δ) q.1 q.2) =ᵐ[(μ.restrict s).prod (μ.restrict s)]
      (fun q => fractionalPairEnergy m (fun x => χ x * (u x - b) / δ) q.1 q.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs)] with q hx hy
    unfold fractionalPairEnergy
    dsimp only
    rw [hone q.1 hx, hone q.2 hy, one_mul, one_mul]
    congr 2
    ring
  refine ⟨(integrable_congr heq).mpr (hE.mono_measure hmeasure), ?_⟩
  rw [integral_congr_ae heq]
  exact integral_mono_measure hmeasure
    (Filter.Eventually.of_forall fun q => fractionalPairEnergy_nonneg m _ q.1 q.2) hE

end

end RieszRectifiability

end OAI
