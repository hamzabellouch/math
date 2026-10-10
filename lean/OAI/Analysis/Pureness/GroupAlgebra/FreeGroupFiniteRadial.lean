import OAI.Analysis.Pureness.Tensor.SpatialRadialTruncation
import OAI.Analysis.Pureness.Tensor.SpatialSubgroupRestriction
import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupFiniteWordBalls
import OAI.Analysis.Pureness.Tensor.SpatialFourierConvergence
import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupWordChoice

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
open Filter Topology
local instance freeGroupFiniteRadialDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
local instance freeGroupFiniteRadialFreeGroupDecidableEq : DecidableEq (FreeGroup ℕ) := Classical.decEq _
variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def freeGroupFiniteBall (n m : ℕ) : Finset (FreeGroup ℕ) :=
  (initialFreeSubgroup_wordBall_finite n m).toFinset.filter (fun g => (canonicalFreeWord g).length < m)

lemma mem_freeGroupFiniteBall (n m : ℕ) (g : FreeGroup ℕ) :
    g ∈ freeGroupFiniteBall n m ↔ g ∈ initialFreeSubgroup n ∧ (canonicalFreeWord g).length < m := by
  classical
  simp only [freeGroupFiniteBall, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, freeGroup_toWord_eq_canonical]
  constructor
  · intro h; exact ⟨h.1.1, h.2⟩
  · intro h; exact ⟨⟨h.1, Nat.le_of_lt h.2⟩, h.2⟩

include hα in
lemma spatialRadialTruncation_generator (r : ℝ) (m : ℕ) (a : A) (g : FreeGroup ℕ) :
    spatialRadialTruncation (X := ℕ) α r m
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ)))) =
    (if (canonicalFreeWord g).length < m then ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ) else 0) •
      spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ))) := by
  apply weighted_operator_partial_sum_apply (fun k => ((r ^ k : ℝ) : ℂ))
    (spatialFreeGroupShell (X := ℕ) α) _ (canonicalFreeWord g).length m
  intro k
  refine (spatialFreeGroupShell_generator α hα k a g).trans ?_
  simp only [freeGroupShellSymbol, freeGroup_toWord_eq_canonical, eq_comm,
    ite_smul, one_smul, zero_smul]

include hα in
lemma finiteRadial_eq_truncation_restriction (r : ℝ) (n m : ℕ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    spatialFiniteFourier (G := FreeGroup ℕ) α (freeGroupFiniteBall n m)
      (fun g => ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ)) x =
      spatialRadialTruncation (X := ℕ) α r m (spatialSubgroupRestriction α (initialFreeSubgroup n) x) := by
  classical
  have hg (a : A) (g : FreeGroup ℕ) :
      spatialFiniteFourier (G := FreeGroup ℕ) α (freeGroupFiniteBall n m)
        (fun g => ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ))
        (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
          (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ)))) =
      spatialRadialTruncation (X := ℕ) α r m (spatialSubgroupRestriction α (initialFreeSubgroup n)
        (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
          (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ))))) := by
    let z := spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ)))
    let R := spatialRadialTruncation (X := ℕ) α r m
    have hu := spatialSubgroupRestriction_generator α hα (initialFreeSubgroup n) a g
    refine (spatialFiniteFourier_generator α hα (freeGroupFiniteBall n m)
      (fun g => ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ)) a g).trans ?_
    by_cases hg : g ∈ initialFreeSubgroup n
    · have he : (if g ∈ freeGroupFiniteBall n m then ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ) else 0) =
          (if (canonicalFreeWord g).length < m then ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ) else 0) := by
        simp only [mem_freeGroupFiniteBall, hg, true_and]
      exact (congrArg (fun c : ℂ => c • z) he).trans
        ((spatialRadialTruncation_generator α hα r m a g).symm.trans
          (congrArg R (hu.trans (ite_eq_left hg))).symm)
    · have he : (if g ∈ freeGroupFiniteBall n m then ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ) else 0) = 0 := by
        simp only [mem_freeGroupFiniteBall, hg, false_and, ↓reduceIte]
      exact (congrArg (fun c : ℂ => c • z) he).trans
        ((zero_smul ℂ z).trans ((map_zero R).symm.trans
          (congrArg R (hu.trans (ite_eq_right hg))).symm))
  refine (spatialGroupPolynomialMap_denseRange (G := FreeGroup ℕ) α).induction_on x ?_ ?_
  · exact isClosed_eq (ContinuousLinearMap.continuous _)
      ((spatialRadialTruncation (X := ℕ) α r m).continuous.comp
        (spatialSubgroupRestriction α (initialFreeSubgroup n)).continuous)
  · intro a
    let R := spatialFiniteFourier (G := FreeGroup ℕ) α (freeGroupFiniteBall n m)
      (fun g => ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ))
    let S := (spatialRadialTruncation (X := ℕ) α r m).comp
      (spatialSubgroupRestriction α (initialFreeSubgroup n))
    let v := fun g => spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
      (a g ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ)))
    exact (congrArg R (spatialGroupPolynomialMap_apply (G := FreeGroup ℕ) α a)).trans
      ((map_sum R v a.support).trans
        ((Finset.sum_congr rfl (fun g _ => hg (a g) g)).trans
          ((map_sum S v a.support).symm.trans
            (congrArg S (spatialGroupPolynomialMap_apply (G := FreeGroup ℕ) α a)).symm)))

include hα in
theorem finiteRadial_norm_le (r : ℝ) (n m : ℕ)
    (hm : ‖spatialRadialTruncation (X := ℕ) α r m‖ ≤ 2)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    ‖spatialFiniteFourier (G := FreeGroup ℕ) α (freeGroupFiniteBall n m)
      (fun g => ((r ^ (canonicalFreeWord g).length : ℝ) : ℂ)) x‖ ≤ 2 * ‖x‖ := by
  apply (congrArg norm (finiteRadial_eq_truncation_restriction α hα r n m x)).trans_le
  exact ((spatialRadialTruncation (X := ℕ) α r m).le_opNorm _).trans
    (mul_le_mul hm (spatialSubgroupRestriction_norm_le α hα (initialFreeSubgroup n) x)
      (norm_nonneg (spatialSubgroupRestriction α (initialFreeSubgroup n) x)) (by norm_num))
end CuntzPureness

end

end OAI
