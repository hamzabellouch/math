import OAI.Analysis.OperatorAlgebra.GNSCyclicRepresentation
import OAI.Analysis.OperatorAlgebra.CyclicSeparatingCompression
import OAI.Analysis.ModularTheory.CommutantExpectation

namespace OAI

/-! A separating vector gives the actual standard GNS representation. -/
noncomputable section
open scoped ComplexOrder Topology
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma gns_bicommutant_separating (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ))
    (hsep : ∀ T : H →L[ℂ] H, T ∈ bicommutant π.range → T ξ = 0 → T = 0)
    (T : gnsHilbert f →L[ℂ] gnsHilbert f)
    (hT : T ∈ bicommutant (gnsBundledHom f).range)
    (hz : T (gnsVector f 1) = 0) : T = 0 := by
  let W := cyclicBundledGNSIsometry f π ξ hf
  apply separating_compression π (gnsBundledHom f) W
    (cyclicBundledGNSIsometry_intertwines f π ξ hf)
    (bicommutant π.range)
    (fun a => subset_bicommutant π.range (π a) ⟨a, rfl⟩)
    (gnsVector f 1) _ T _ hz
  · intro U hU hzero
    apply hsep U hU
    rw [← cyclicBundledGNSIsometry_one f π ξ hf]
    exact hzero
  · intro R hR
    exact VonNeumannAlgebra.mem_commutant_iff.mp hT R
      ((mem_commutantOf_iff _ _).mpr (by
        rintro _ ⟨a, rfl⟩
        exact hR a))

def standardGNSData (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ))
    (hsep : ∀ T : H →L[ℂ] H, T ∈ bicommutant π.range → T ξ = 0 → T = 0) :
    CyclicSeparatingData (gnsHilbert f) where
  M := bicommutant (gnsBundledHom f).range
  xi := gnsVector f 1
  norm_xi := by
    calc
      ‖gnsVector f 1‖ = ‖cyclicBundledGNSIsometry f π ξ hf (gnsVector f 1)‖ :=
        ((cyclicBundledGNSIsometry f π ξ hf).norm_map _).symm
      _ = 1 := by rw [cyclicBundledGNSIsometry_one, hξ]
  cyclic := by
    apply (gnsBundledHom_cyclic f).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨gnsBundledHom f a, subset_bicommutant _ _ ⟨a, rfl⟩, rfl⟩
  separating := gns_bicommutant_separating f π ξ hf hsep

end WeakPureInfiniteness

end

end OAI
