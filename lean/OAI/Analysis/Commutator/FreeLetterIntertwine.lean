import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry14
import OAI.Analysis.Commutator.FreeAction
import OAI.Analysis.Commutator.FreeInnerFamily
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

lemma letterGNSIso_value (x : letterSpace t S i) (d : D) (hd : f d=letterValue t S i x) :
    (letterGNSIso t f hf S i hS (x : Completion (letterSpace t S i)) :
      (factorTrace t f hf).GNS)=TracialGNS.algebraVector (factorTrace t f hf) d := by
  let xp : HilbertCompletion.centered ((pullbackState t f hf).functional.toPreGNS 1) :=
    ⟨(pullbackState t f hf).functional.toPreGNS d,by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right,inner_pre_one]
      change t.functional (f d)=0
      rw [hd]
      exact x.property.2⟩
  have hx : letterPreMap t f hf S i hS xp=x := by
    apply Subtype.ext
    change t.functional.toPreGNS (f d)=(x : preSpace t)
    rw [hd]
    exact PositiveLinearMap.toPreGNS_ofPreGNS _ _
  have h := letterGNSIso_pre t f hf S i hS xp
  rw [hx] at h
  exact h

variable (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

include ht in
lemma factorTrace_tracial (a b : D) :
    factorTrace t f hf (a*b)=factorTrace t f hf (b*a) := by
  change t.functional (f (a*b))=t.functional (f (b*a))
  simp only [map_mul,ht]

lemma letterGNSIso_conjugation (u : unitary D) (x : letterSpace t S i) :
    letterGNSIso t f hf S i hS
      (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
        (innerFamily_trace t ht f i u) i x : Completion (letterSpace t S i)) =
    centeredIsometry (TracialGNS.vacuum (factorTrace t f hf))
      (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (TracialGNS.conjugation_vacuum (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (letterGNSIso t f hf S i hS (x : Completion (letterSpace t S i))) := by
  have hxm : letterValue t S i x ∈ f.range := hS ▸ x.property.1
  obtain ⟨d,hd⟩ := hxm
  change f d=letterValue t S i x at hd
  have hd' : f ((u:D)*d*star (u:D)) = letterValue t S i
      (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
        (innerFamily_trace t ht f i u) i x) := by
    change f ((u:D)*d*star (u:D))=innerFamily f i u i (letterValue t S i x)
    rw [innerFamily_self,map_mul,map_mul,hd]
  apply Subtype.ext
  change (letterGNSIso t f hf S i hS
      (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
        (innerFamily_trace t ht f i u) i x : Completion (letterSpace t S i)) :
      (factorTrace t f hf).GNS) =
    TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u
      (letterGNSIso t f hf S i hS (x : Completion (letterSpace t S i)) :
        (factorTrace t f hf).GNS)
  rw [letterGNSIso_value t f hf S i hS _ _ hd',
    letterGNSIso_value t f hf S i hS x d hd]
  exact (TracialGNS.conjugation_coe (factorTrace t f hf) (factorTrace_tracial t f hf ht) u d).symm

end Kadison.FreeBlocks

end

end
end

end OAI
