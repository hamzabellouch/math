import OAI.Analysis.Nuclearity.QuotientTensorNorm
import OAI.Analysis.Nuclearity.NuclearUnitizationCPAP
import OAI.Analysis.PureInfiniteness.AbsorptionFromQuotientNuclearity

namespace OAI

/-! Application of the proved quotient tensor bound to the exact represented
unitization input in Corollary 1.3 (Choi--Effros, Corollary 3.3). -/
noncomputable section
open Filter TopologicalSpace
open scoped ComplexOrder
namespace WeakPureInfiniteness

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeparableSpace A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma representedQuotient_separable {D : Type v} [CStarAlgebra D]
    (φ : A →⋆ₐ[ℂ] D) : SeparableSpace (representedAlgebra φ) :=
  (representedQuotientMap_surjective φ).denseRange.separableSpace
    (nonUnitalStarHom_continuous (representedQuotientMap φ).toNonUnitalStarAlgHom)

theorem nuclear_represented_quotient_tensorNorm {D : Type v} [CStarAlgebra D]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) (hA : Nuclear A)
    (φ : A →⋆ₐ[ℂ] D) : Pureness.IsNuclear.{v,v} (representedAlgebra φ) := by
  let : SeparableSpace (representedAlgebra φ) := representedQuotient_separable φ
  let _ : PartialOrder (representedAlgebra φ) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (representedAlgebra φ) := CStarAlgebra.spectralOrderedRing _
  exact nuclear_quotient_tensorNorm ω hω hA (representedQuotientMap φ)
    (representedQuotientMap_surjective φ)

section Nonunital
variable {N : Type u} [NonUnitalCStarAlgebra N] [SeparableSpace N]
  [PartialOrder N] [StarOrderedRing N]

omit [PartialOrder N] [StarOrderedRing N] in
lemma unitization_separable : SeparableSpace (Unitization ℂ N) :=
  (Unitization.uniformEquivProd (𝕜 := ℂ) (A := N)).symm.surjective.denseRange.separableSpace
    (Unitization.uniformEquivProd (𝕜 := ℂ) (A := N)).symm.toHomeomorph.continuous

theorem nuclear_unitizedFactorImageNuclear
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) (hN : Nuclear N) :
    UnitizedFactorImageNuclear N := by
  let : SeparableSpace (Unitization ℂ N) := unitization_separable
  let _ : PartialOrder (Unitization ℂ N) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (Unitization ℂ N) := CStarAlgebra.spectralOrderedRing _
  intro B _ H π _hfactor
  exact nuclear_represented_quotient_tensorNorm ω hω (nuclear_unitization_cpap hN)
    (leftRepresentedMap π)

end Nonunital
end WeakPureInfiniteness

end

end OAI
