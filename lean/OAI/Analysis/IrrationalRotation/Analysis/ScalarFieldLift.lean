import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

namespace Invariant233.DirectIntegral

open MeasureTheory Filter
open scoped ENNReal

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_smul_id_of_representation_ae_scalar
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hrep : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (c : ℂ) (hc : ∀ᵐ x ∂μ, A x = c • (1 : E →L[ℂ] E)) :
    T = c • (1 : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hrep f, hc, Lp.coeFn_smul c f] with x hfx hcx hsmul
  change (T f) x = (c • f) x
  rw [hfx, hcx]
  change c • f x = (c • f) x
  exact hsmul.symm

theorem scalar_of_representation_ae_scalar
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hrep : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (hc : ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : E →L[ℂ] E)) :
    ∃ c : ℂ, T = c • (1 : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, eq_smul_id_of_representation_ae_scalar T A hrep c hc⟩

end Invariant233.DirectIntegral

end OAI
