import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Every coupling to a Dirac measure has the same transport cost

This identifies the limiting radial plan as optimal without retaining
an extra optimality assumption in the concentration argument.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem transportCost_eq_moment_of_dirac (ν : Measure X) (p : X)
    (π : Measure (X × X)) (h₀ : π.map Prod.fst = ν)
    (h₁ : π.map Prod.snd = Measure.dirac p) :
    transportCost π = ∫⁻ x, ENNReal.ofReal (dist x p) ^ 2 ∂ν := by
  have hp : ∀ᵐ xy ∂π, xy.2 = p := by
    apply ae_of_ae_map (μ := π) measurable_snd.aemeasurable (p := fun x : X => x = p)
    rw [h₁]
    simp
  have hm : Measurable (fun x : X => ENNReal.ofReal (dist x p) ^ 2) := by fun_prop
  rw [← h₀, lintegral_map hm measurable_fst]
  unfold transportCost
  apply lintegral_congr_ae
  filter_upwards [hp] with xy hxy
  rw [hxy]

theorem isOptimalCoupling_of_dirac (ν : Measure X) (p : X)
    (π : Measure (X × X)) (h₀ : π.map Prod.fst = ν)
    (h₁ : π.map Prod.snd = Measure.dirac p) :
    IsOptimalCoupling ν (Measure.dirac p) π := by
  refine ⟨h₀, h₁, ?_⟩
  intro π' h₀' h₁'
  rw [transportCost_eq_moment_of_dirac ν p π h₀ h₁,
    transportCost_eq_moment_of_dirac ν p π' h₀' h₁']

end RegularPointCoordinates

end OAI
