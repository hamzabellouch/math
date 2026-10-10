import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace ClosedFunctionAlgebra
open scoped BigOperators CStarAlgebra

variable {X A : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [CStarAlgebra A]
local instance (priority := 2000) functionSemiring : Semiring C(X,A) :=
  (inferInstance : Ring C(X,A)).toSemiring
 def realScalar (g : C(X,ℝ)) : C(X,A) := ⟨fun x => g x • (1:A),by fun_prop⟩
 theorem mem_of_fibrewise (S : StarSubalgebra ℂ C(X,A)) (hS : IsClosed (S : Set C(X,A)))
    (hscalar : ∀ g : C(X,ℝ),realScalar (A := A) g∈S) (f : C(X,A))
    (hf : ∀ x : X,∃ g∈S,g x=f x) : f∈S := by
  classical
  change f∈(S : Set C(X,A))
  rw [←hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  choose g hg he using hf
  let U : X→Set X := fun x => {y | ‖f y-g x y‖<ε/2}
  have ho (x : X) : IsOpen (U x) := isOpen_lt (by fun_prop) continuous_const
  have hc : (Set.univ : Set X)⊆⋃ x,U x := by
    intro y _
    apply Set.mem_iUnion.mpr
    exact ⟨y,by simp only [U,Set.mem_ofPred_eq,he,sub_self,norm_zero]; linarith⟩
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U ho hc
  have hcover : (Set.univ : Set X)⊆⋃ i : t,U i := by
    intro y hy
    obtain ⟨i,hi,hy⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hy⟩
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun i : t => U i) (fun i => ho i) (locallyFinite_of_finite _) hcover
  have hsum (x : X) : ∑ i : t,ρ i x=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
  let F : C(X,A) := ∑ i : t,realScalar (ρ i)*g i
  have hF : F∈S := S.sum_mem (fun i _ => S.mul_mem (hscalar _) (hg i))
  have hnorm : ‖F-f‖≤ε/2 := by
    apply (ContinuousMap.norm_le _ (by linarith : (0:ℝ)≤ε/2)).mpr
    intro x
    have heval : (F-f) x=∑ i : t,ρ i x • (g i x-f x) := by
      change ((∑ i : t,realScalar (ρ i)*g i) : C(X,A)) x-f x=_
      simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply,realScalar,ContinuousMap.coe_mk,
        smul_mul_assoc,one_mul,smul_sub,Finset.sum_sub_distrib]
      rw [←Finset.sum_smul,hsum,one_smul]
    rw [heval]
    calc
      ‖∑ i : t,ρ i x • (g i x-f x)‖≤∑ i : t,‖ρ i x • (g i x-f x)‖ := norm_sum_le _ _
      _≤∑ i : t,ρ i x*(ε/2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_of_nonneg (ρ.nonneg i x)]
        by_cases hz : ρ i x=0
        · simp [hz]
        · apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i x)
          have hx : x∈U i := hρ i (subset_closure hz)
          exact (by simpa only [U,Set.mem_ofPred_eq,norm_sub_rev] using hx : ‖g i x-f x‖<ε/2).le
      _=ε/2 := by rw [←Finset.sum_mul,hsum,one_mul]
  refine ⟨F,hF,?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  exact hnorm.trans_lt (half_lt_self hε)
end ClosedFunctionAlgebra

end
end

end OAI
