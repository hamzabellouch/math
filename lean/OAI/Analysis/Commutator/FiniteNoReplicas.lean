import Mathlib
import OAI.Analysis.Commutator.PartialDecomposition
import OAI.Analysis.Commutator.PartialDecompositionCountable
import OAI.Analysis.Commutator.ProperIsometryReplicas
import OAI.Analysis.Commutator.ReplicaPacking

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem finite_no_replicas (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {r : H →L[ℂ] H} (hrM : r∈M) (hr : IsStarProjection r) (hrn : r≠0)
    (R : Replicas M r) : False := by
  classical
  obtain ⟨D⟩ := exists_partialDecomposition M hfac hrM hr hrn
  have := D.countable
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
  have hsi : star s*s=1 := D.packing_isometry R hr f hf hsv
  have hti : star t*t=1 := D.packing_isometry R hr g hg htv
  have hst : star s*t=0 := D.packings_orthogonal R f g hfg hsv htv
  have hsf : s*star s=1 := hfin s hs hsi
  have htz : t=0 := by
    calc
      t=(s*star s)*t := by rw [hsf,one_mul]
      _=0 := by rw [mul_assoc,hst,mul_zero]
  have hone : (1 : H →L[ℂ] H)=0 := by simpa only [htz,mul_zero] using hti.symm
  exact hrn (by simpa only [mul_one,mul_zero] using congrArg (fun z : H →L[ℂ] H => r*z) hone)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
