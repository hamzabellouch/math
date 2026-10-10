import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationDegreeBound
import OAI.Combinatorics.Chromatic.Walls.LaurentCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma mutation_infinity_lower_bound {n : ℕ} {m : M}
    (hm : HasRootDegree (mutatedRoots Ω C pc) n m) :
    -(mutationSize Ω C pc:ℤ)*nonpDegree (mutatedCoordinates Ω C coord pc) pc m ≤
      -pureDegree coord pc m := by
  obtain ⟨d,hd,hc,hC⟩:=root_coordinates (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) hm
  have hn (i : I) : 0 ≤ mutatedCoordinates Ω C coord pc m i := by
    rw [hc]
    exact Int.natCast_nonneg _
  have hs : (∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
      mutatedCoordinates Ω C coord pc m i) ≤
      (mutationSize Ω C pc:ℤ)*nonpDegree (mutatedCoordinates Ω C coord pc) pc m := by
    change _ ≤ (mutationSize Ω C pc:ℤ)*(∑i∈Finset.univ.erase pc,
      mutatedCoordinates Ω C coord pc m i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hn i)
    exact (max_le (abs_nonneg _) (neg_le_abs _)).trans
      (mutationSize_bound Ω C pc i (Finset.mem_erase.mp hi).1)
  have hk : pureDegree coord pc m = -mutatedCoordinates Ω C coord pc m pc+
      ∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
        mutatedCoordinates Ω C coord pc m i := by
    have H:=congrArg (fun f : I → ℤ => f pc)
      (mutatedCoefficientMap_involutive pc (mutationPairing Ω C pc) (coord m))
    rw [mutatedCoefficientMap_at] at H
    exact H.symm
  have hp:=hn pc
  nlinarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
