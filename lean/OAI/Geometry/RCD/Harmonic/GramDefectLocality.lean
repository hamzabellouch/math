import OAI.Geometry.RCD.Harmonic.GramDefect
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # Locality of the finite Gram matrix error -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem gramDefect_congr_ae (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} {u U : Fin n → SobolevSpace μ Q} {Ω : Set X}
    (hu : ∀ i, SobolevSpace.toLp μ Q (U i) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q (u i)) :
    gramDefect μ Q U =ᵐ[μ.restrict Ω] gramDefect μ Q u := by
  have hG (i j : Fin n) := localGamma_pair_congr_ae μ Q (hu i) (hu j)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hG i))] with x hx
  unfold gramDefect
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hx i j]))

end RegularPointCoordinates

end

end OAI
