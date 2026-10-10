import OAI.Analysis.IrrationalRotation.Rotation.ContinuousWeightAssembly
import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleCocycle

namespace OAI

open MeasureTheory Filter Set

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurableWeight_ae_exp_neg_rawCost :
    p.measurableWeight θ =ᵐ[circleMeasure] fun x => Real.exp (-p.rawCost θ x) := by
  obtain ⟨s, hs, hfull, hinv, hfinite, hcoc⟩ := hp.exists_parameter_cocycle_set
  filter_upwards [hfull] with x hx
  have h := p.floorCocycle_eq_block_sum θ 1 x (hfinite x hx 1)
  change p.floorCocycle θ 1 x = _
  simpa only [Int.cast_one, one_mul, Finset.mul_sum,
    CircleParameterData.rawCost, CircleParameterData.rawBlock] using h

theorem exists_continuousWeight_parameter_factor_domain (d : BackgroundBumpData θ) :
    ∃ s : Set Circle, MeasurableSet s ∧ circleMeasure sᶜ = 0 ∧
      (∀ n : ℤ, ((Equiv.addRight (θ : Circle)) ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ (k + 1)) x)) *
          p.continuousWeight θ d (((Equiv.addRight (θ : Circle)) ^ k) x) =
        Real.exp (-1) * p.measurableWeight θ (((Equiv.addRight (θ : Circle)) ^ k) x) *
          Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ k) x)) :=
  hp.exists_continuousWeight_factor_domain d (p.measurableWeight θ)
    hp.measurable_parameter_weight hp.measurableWeight_ae_exp_neg_rawCost

end Invariant233.CircleParameterLaws

end OAI
