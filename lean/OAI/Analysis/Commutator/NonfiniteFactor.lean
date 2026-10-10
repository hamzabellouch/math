import Mathlib
import OAI.Analysis.Commutator.PartialDecomposition
import OAI.Analysis.Commutator.ProperIsometryReplicas
import OAI.Analysis.Commutator.ProperlyInfiniteMain
import OAI.Analysis.Commutator.PartialDecompositionCountable
import OAI.Analysis.Commutator.ReplicaPacking

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem nonfinite_two_isometries (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : ¬IsFiniteAlgebra M) :
    ∃ s t : M,star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  obtain ⟨r,hrM,hr,hrn,⟨R⟩⟩ := nonfinite_replicas M hfin
  obtain ⟨D⟩ := exists_partialDecomposition M hfac hrM hr hrn
  let := D.countable
  obtain ⟨e,he⟩ := Countable.exists_injective_nat (D.I × Bool)
  let f : D.I → ℕ := fun i => e (i,false)
  let g : D.I → ℕ := fun i => e (i,true)
  have hf : Function.Injective f := fun i j h => (Prod.mk.inj (he h)).1
  have hg : Function.Injective g := fun i j h => (Prod.mk.inj (he h)).1
  have hfg : ∀ i j,f i≠g j := by
    intro i j hij
    have := (Prod.mk.inj (he hij)).2
    contradiction
  obtain ⟨s,hs,hsv⟩ := D.exists_packing R hr f hf
  obtain ⟨t,ht,htv⟩ := D.exists_packing R hr g hg
  refine ⟨⟨s,hs⟩,⟨t,ht⟩,?_,?_,?_⟩
  · apply Subtype.ext
    exact D.packing_isometry R hr f hf hsv
  · apply Subtype.ext
    exact D.packing_isometry R hr g hg htv
  · apply Subtype.ext
    exact D.packings_orthogonal R f g hfg hsv htv

end Kadison.PartialIsometryOrder

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_nonfinite_factor (P : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor P) (hfin : ¬PartialIsometryOrder.IsFiniteAlgebra P)
    (Y : H →L[ℂ] H) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨s,t,hs,ht,hst⟩ := PartialIsometryOrder.nonfinite_two_isometries P hfac hfin
  exact uniform_commutator_of_two_isometries P s t hs ht hst Y h X hX

end Kadison

end

end
end

end OAI
