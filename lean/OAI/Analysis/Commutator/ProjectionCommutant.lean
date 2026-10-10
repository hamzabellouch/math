import Mathlib
import OAI.Analysis.Commutator.SelfAdjointSpectral
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannIntersection (M N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := M.toStarSubalgebra ⊓ N.toStarSubalgebra
  centralizer_centralizer' := by
    apply Set.Subset.antisymm
    · intro a ha
      constructor
      · have hh := Set.centralizer_subset (Set.centralizer_subset
          (show ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆ (M : Set (H →L[ℂ] H)) from fun _ h => h.1)) ha
        simpa only [VonNeumannAlgebra.centralizer_centralizer,VonNeumannAlgebra.coe_toStarSubalgebra] using hh
      · have hh := Set.centralizer_subset (Set.centralizer_subset
          (show ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆ (N : Set (H →L[ℂ] H)) from fun _ h => h.2)) ha
        simpa only [VonNeumannAlgebra.centralizer_centralizer,VonNeumannAlgebra.coe_toStarSubalgebra] using hh
    · exact Set.subset_centralizer_centralizer

@[simp] lemma mem_vonNeumannIntersection (M N : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    a∈vonNeumannIntersection M N ↔ a∈M ∧ a∈N := Iff.rfl

theorem commutes_algebra_of_commutes_projections (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ p∈M,IsStarProjection p → T*p=p*T) :
    ∀ a∈M,T*a=a*T := by
  have hself : ∀ a∈M,IsSelfAdjoint a → T*a=a*T := by
    intro a ha hsa
    have hclosed : IsClosed {b : H →L[ℂ] H | T*b=b*T} := isClosed_eq
      (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    apply hclosed.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n,p,c,hp,_,he⟩ := Polar.exists_selfadjoint_spectral_sum M ha hsa hε
    refine ⟨∑ i,c i • p i,?_,?_⟩
    · change T*(∑ i,c i • p i)=(∑ i,c i • p i)*T
      simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun z : H →L[ℂ] H => c i • z)
        (hT (p i) (hp i).1 (hp i).2))
    · simpa only [dist_eq_norm] using he
  intro a ha
  let b : M := ⟨a,ha⟩
  have hR := hself (((realPart b):M):H →L[ℂ] H) ((realPart b):M).property
    ((realPart b).property.map M.toStarSubalgebra.subtype)
  have hI := hself (((imaginaryPart b):M):H →L[ℂ] H) ((imaginaryPart b):M).property
    ((imaginaryPart b).property.map M.toStarSubalgebra.subtype)
  have hid : (((realPart b):M):H →L[ℂ] H)+
      Complex.I • (((imaginaryPart b):M):H →L[ℂ] H)=a :=
    congrArg (fun x : M => (x:H →L[ℂ] H)) (realPart_add_I_smul_imaginaryPart b)
  rw [←hid,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,hR,hI]

end Kadison

end

end
end

end OAI
