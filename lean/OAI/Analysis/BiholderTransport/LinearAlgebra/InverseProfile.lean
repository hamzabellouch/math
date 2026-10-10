import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FixedJoinSmooth
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder
import OAI.Analysis.BiholderTransport.Regularity.FixedJoinMiddle

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma symmetric_eigenvalue_pos {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hn : finrank ℝ E=n) (hpos : ∀ x:E, x≠0 → 0 < inner ℝ (A x) x) (i:Fin n) :
    0 < hA.eigenvalues hn i := by
  have H := hpos (hA.eigenvectorBasis hn i) ((hA.eigenvectorBasis hn).toBasis.ne_zero i)
  rw [hA.apply_eigenvectorBasis,real_inner_smul_left,real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).norm_eq_one] at H
  simpa using H
end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

local instance tangentFiniteJoin (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def fixedJoinOperator (x : M) (h T : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  exact bilinearOperator (fixedJoinMiddle x h T p)

@[simp] lemma fixedJoinOperator_inner (x : M) (h T : ℝ)
    (p d k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (fixedJoinOperator x h T p d) k=fixedJoinMiddle x h T p d k :=
  bilinearOperator_inner _ d k

lemma fixedJoinOperator_symmetric {x:M} {h T:ℝ} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p)) :
    (fixedJoinOperator x h T p).toLinearMap.IsSymmetric :=
  bilinearOperator_symmetric (fixedJoinMiddle_symmetric hB)

variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinAction_shortened_contDiffAt {x : M} {h T:ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hh1 : h < 1) (hT : h < T) (hT1 : T < 1)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  have hden : 0 < 1-h := sub_pos.mpr hh1
  have ht0 : 0 < (T-h)/(1-h) := div_pos (sub_pos.mpr hT) hden
  have ht1 : (T-h)/(1-h) < 1 := (div_lt_one hden).mpr (by linarith)
  have H := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors _ hright) ht0 ht1
  rw [smul_smul,div_mul_cancel₀ _ hden.ne'] at H
  exact fixedJoinAction_contDiffAt hT.ne' hleft H
end WeakMTWTransport

end

end OAI
