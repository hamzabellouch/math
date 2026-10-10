import Mathlib
import OAI.Analysis.Commutator.CyclicSpatialImplementation
import OAI.Analysis.Commutator.RectangularColumn

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open OperatorAmplification CyclicColumns ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → lam a x∈K)

local instance : NormedAddCommGroup (K →L[ℂ] H) := ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℂ (K →L[ℂ] H) := ContinuousLinearMap.toNormedSpace

theorem extension_amplified_bound_unconditional (M : VonNeumannAlgebra H)
    (hlam : Function.Injective lam) (hrange : Set.range lam=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K)
    (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω)) :
    WOTDistance.AmplifiedBound M (extendZero (K:=K) G) (16*‖delta lam K hinv G‖) := by
  have hh := extension_amplified_bound lam K hinv M hlam hrange G Ω hΩ
    (c:=4*‖delta lam K hinv G‖) (by positivity)
    (fun _ v ζ => RectangularColumn.column_bound (restrict lam K hinv) lam
      (delta lam K hinv G) (delta_derivation lam K hinv G) v ζ)
  convert hh using 1
  ring

theorem exists_cyclic_intertwiner_unconditional (M : VonNeumannAlgebra H)
    (hlam : Function.Injective lam) (hrange : Set.range lam=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K)
    (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω)) :
    ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (restrict lam K hinv a)=(lam a).comp T) ∧
      ‖G-T‖≤16*‖delta lam K hinv G‖ := by
  obtain ⟨T,hT,hn⟩ := exists_cyclic_intertwiner lam K hinv M hlam hrange G Ω hΩ
    (c:=4*‖delta lam K hinv G‖) (by positivity)
    (fun _ v ζ => RectangularColumn.column_bound (restrict lam K hinv) lam
      (delta lam K hinv G) (delta_derivation lam K hinv G) v ζ)
  refine ⟨T,hT,?_⟩
  nlinarith

end Kadison.CyclicSpatial

end

end
end

end OAI
