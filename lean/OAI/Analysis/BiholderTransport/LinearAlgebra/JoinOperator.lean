import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Diagonal
import OAI.Analysis.BiholderTransport.CostGeometry.SplitEndpoint
import OAI.Analysis.BiholderTransport.LinearAlgebra.JoinCongruence
import OAI.Analysis.BiholderTransport.Coordinates.UniformLog

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section JoinOperator
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def splitJoinHessianOperator (x : M) (t : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p)).bilinearComp
      (inr ℝ _ _) (inr ℝ _ _))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_splitJoinHessianOperator (x : M) (t : ℝ)
    (p a k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (splitJoinHessianOperator x t p a) k=
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,a) (0,k) :=
  InnerProductSpace.toDual_symm_apply

lemma splitJoinHessianOperator_positive {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    (splitJoinHessianOperator x t p).toLinearMap.IsPositive := by
  have hleft := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp ht ht1 le_rfl
  have hB := diagonalSplitAction_contDiffAt hleft hright
  refine ⟨?_,?_⟩
  · intro a k
    change inner ℝ (splitJoinHessianOperator x t p a) k=
      inner ℝ a (splitJoinHessianOperator x t p k)
    rw [real_inner_comm (splitJoinHessianOperator x t p k) a,
      inner_splitJoinHessianOperator,inner_splitJoinHessianOperator]
    exact (hB.isSymmSndFDerivAt (by simp)).eq _ _
  · intro a
    change 0 ≤ inner ℝ (splitJoinHessianOperator x t p a) a
    rw [inner_splitJoinHessianOperator]
    obtain ⟨P,hP,HP⟩ := split_join_hessian_congruence hp ht ht1
    rw [HP]
    exact middleHessian_one_nonneg hp ht ht1 _

lemma uniform_join_endpoint_factorization :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4),
      ∃ L : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
          TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
        Function.Bijective L ∧ (∀ v, c*‖v‖≤‖L v‖ ∧ ‖L v‖≤C*‖v‖) ∧ ∀ a k,
          inner ℝ (splitJoinHessianOperator x t p a) k=
            inner ℝ (L k) (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
              (riemannianExp x) p a)/(1-t) := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_suffix_log_derivative_bounds (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp t ht
  have htpos : 0<t := by linarith [ht.1]
  have htone : t<1 := by linarith [ht.2]
  have hleft := contracted_minimizer_mem_injectivityDomain hp htpos htone
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp htpos htone le_rfl
  obtain ⟨q,hq,hqI,hqr⟩ := exists_suffix_log_in_prefix_coordinates hright
  have hqd := hq.differentiableAt (by simp)
  have hLi := prefix_log_fderiv_injective htpos.ne' hleft hqd hqr
  have hLs : Function.Surjective (fderiv ℝ q p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ q p).toLinearMap) rfl).mp hLi
  refine ⟨fderiv ℝ q p,⟨hLi,hLs⟩,H x p hp t ht q hqd hqI.self_of_nhds hqr,?_⟩
  intro a k
  rw [inner_splitJoinHessianOperator,
    diagonalSplitAction_hessian_identity htpos htone hleft hright]
  have hsym := (diagonalSplitAction_contDiffAt hleft hright).isSymmSndFDerivAt
    (by simp)
  rw [hsym.eq (a,0) (0,k),diagonalSplitAction_mixed_endpoint hleft hright hqd hqI hqr]
  ring

end JoinOperator
end WeakMTWTransport

end

end

end

end OAI
