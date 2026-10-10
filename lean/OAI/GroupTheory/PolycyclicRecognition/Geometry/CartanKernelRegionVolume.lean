import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeKernelVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel

namespace OAI

/-! # Kernel-box volume for the actual Cartan ideal coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

theorem exists_cone_kernel_box_volumes
    (C : Set (H →ₗ[ℝ] ℝ)) {Q : Type*} [Group Q] (π : F.N.carrier →* Q)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ι : I.carrier →* F.N.carrier) (hι : Topology.IsClosedEmbedding ι)
    (hrange : range ι = (π.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ι (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let μK := Measure.map (kernelRealization π ι hι hrange) μI
    let RI := fun n => exponentialIdealKernelRegion (M.coneWordIdeal C) π
      (F.ExpN ∘ F.N.equiv) {i | ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ R n}
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n, μK (RI n) ≠ ⊤ ∧ (μK (RI n)).toReal = V n *
        Real.exp ((∑ j, M.coneIdealWordCost C s (β.val j)) * scale n) :=
  exists_exponential_kernel_box_volumes (M.coneWordIdeal C) π ι hι hrange
    (F.ExpN ∘ F.N.equiv) haarI ExpI hExpI I.equiv (M.coneIdeal_nilpotent C) hIExp
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    (fun j => M.coneIdealWordCost C s (β.val j)) μI scale R hscale hR0 hR

end PolycyclicRecognition.CartanWordModel

end

end OAI
