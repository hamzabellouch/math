import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLogRegionVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel

namespace OAI

/-! # The log-region volume theorem for the actual Cartan factor -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

theorem CartanFactorModel.log_regions_volume
    (haar : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbij : Function.Bijective F.ExpD)
    (μ : Measure F.D.carrier) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let B := fun n => {d : F.D.carrier |
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbij d)‖ ≤ R n}
    (∀ n, μ (B n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (B n)).toReal) :=
  cartan_log_regions_volume (L := GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (E := F.D.modelSpace) (D := F.D.carrier) H haar F.ExpD F.isExpD
    F.D.equiv hbij μ scale R hs hR0 hR

end PolycyclicRecognition

end

end OAI
