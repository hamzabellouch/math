import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition
import OAI.Analysis.KadisonKastler.NearSeparableGenerators

namespace OAI

/-! # Selecting and assembling implementers in a common central decomposition -/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_bounded_conjugacy_from_centralPair
    (hK : PublishedKaplanskyDensity.{u}) (hSelect : PublishedUnitaryBorelSelection.{u, u})
    (M N : VonNeumannAlgebra H) (A B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    (hAs : IsSeparable (A : Set (H →L[ℂ] H)))
    (hBs : IsSeparable (B : Set (H →L[ℂ] H)))
    {hAC : A ≤ C} {hBC : B ≤ C} (D : CentralPairDecomposition M N A B C hAC hBC)
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ n, ∀ᵐ x ∂(D.stratum n).μ,
      ∃ v : unitary ((D.stratum n).K →L[ℂ] (D.stratum n).K),
        Conjugates v
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hAC)).range)
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hBC)).range) ∧
        ‖(v : (D.stratum n).K →L[ℂ] (D.stratum n).K) - 1‖ ≤ a) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ ≤ a := by
  let := StarSubalgebra.cstarAlgebra A (h_closed := hAc)
  let := StarSubalgebra.cstarAlgebra B (h_closed := hBc)
  let : SeparableSpace A := hAs.separableSpace
  let : SeparableSpace B := hBs.separableSpace
  obtain ⟨sA, hsA, hdA⟩ := exists_norm_dense_unitBall_sequence A
  obtain ⟨sB, hsB, hdB⟩ := exists_norm_dense_unitBall_sequence B
  apply exists_bounded_conjugacy_of_spatialTransport D.coordinates M N
  apply exists_bounded_conjugacy_of_block_implementers D.leftBlocks D.rightBlocks ha
  intro n
  let φA (x : (D.stratum n).X) :=
    (D.representation n x).comp (StarSubalgebra.inclusion hAC)
  let φB (x : (D.stratum n).X) :=
    (D.representation n x).comp (StarSubalgebra.inclusion hBC)
  let SA (x : (D.stratum n).X) := quotientStrongUnitBallTests hK (φA x) sA hsA hdA
  let SB (x : (D.stratum n).X) := quotientStrongUnitBallTests hK (φB x) sB hsB hdB
  apply exists_bounded_conjugacy_of_fiber_implementers hSelect (D.stratum n).μ
    (fun x => generatedVonNeumannAlgebra (φA x).range)
    (fun x => generatedVonNeumannAlgebra (φB x).range)
    (D.leftBlock n) (D.rightBlock n) (D.leftFields n) (D.rightFields n) SA SB
  · intro j ξ
    exact D.representation_measurable n (StarSubalgebra.inclusion hAC (sA j)) ξ
  · intro j ξ
    exact D.representation_measurable n (StarSubalgebra.inclusion hBC (sB j)) ξ
  · exact ha
  · exact hex n

end

end KadisonKastler

end OAI
