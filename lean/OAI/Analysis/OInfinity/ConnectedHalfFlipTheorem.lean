import OAI.Analysis.Nuclearity.TensorHalfFlipApplication
import OAI.Analysis.OInfinity.ConnectedGeneratorWitness

namespace OAI

/-! The connected approximate inner half-flip of O∞, obtained from the
actual finite connected conjugacy of its two commuting tensor-factor rows.
This is the specialization of Kirchberg (2006), Proposition 4.4(3),(5)
and Remark 4.6 needed by the nonunital absorption criterion. -/

noncomputable section
open Filter
open scoped TensorProduct

namespace WeakPureInfiniteness

variable {T : Type*} [CStarAlgebra T]

theorem oInfinity_connectedHalfFlip
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T) :
    CStarAbsorption.ConnectedApproximateInnerHalfFlip f := by
  classical
  rcases subsingleton_or_nontrivial T with hT | hT
  · let := hT
    exact connectedHalfFlip_of_subsingleton f
  · let := hT
    let U := Ultrafilter.of (atTop : Filter ℕ)
    let : Fact ((U : Filter ℕ) ≤ atTop) := ⟨Ultrafilter.of_le _⟩
    apply oInfinity_connectedHalfFlip_of_generators f
    intro N δ hδ
    simpa only [tensorOInfinityLeftHom_apply, tensorOInfinityRightHom_apply] using
      oInfinity_connected_generator_conjugacy U
        (tensorOInfinityLeftHom f) (tensorOInfinityRightHom f)
        (tensorOInfinity_factors_commute f) N δ hδ

end WeakPureInfiniteness

end

end OAI
