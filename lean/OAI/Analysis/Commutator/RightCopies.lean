import Mathlib
import OAI.Analysis.Commutator.HilbertPadding

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification CyclicColumns

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance rightCopiesSourceDecidableEq : DecidableEq ι := Classical.decEq ι

local instance rightCopiesPaddingDecidableEq : DecidableEq κ := Classical.decEq κ

def rightCopies : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=H) (κ⊕ι) where
  toFun v := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => v i))
  map_add' v w := by ext i; cases i <;> simp
  map_smul' z v := by ext i; cases i <;> simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2,Fintype.sum_sum_type]

omit [CompleteSpace H] in
@[simp] lemma rightCopies_inl (v : SumSpace (H:=H) ι) (k : κ) :
    rightCopies ι κ v (Sum.inl k)=0 := rfl

omit [CompleteSpace H] in
@[simp] lemma rightCopies_inr (v : SumSpace (H:=H) ι) (i : ι) :
    rightCopies ι κ v (Sum.inr i)=v i := rfl

lemma rightCopies_diagonal (a : H →L[ℂ] H) :
    (diagonal (H:=H) (κ⊕ι) a).comp (rightCopies (H:=H) ι κ).toContinuousLinearMap=
      (rightCopies (H:=H) ι κ).toContinuousLinearMap.comp (diagonal (H:=H) ι a) := by
  ext v i
  cases i <;> simp

lemma rightCopies_adjoint_diagonal (a : H →L[ℂ] H) :
    (rightCopies (H:=H) ι κ).toContinuousLinearMap.adjoint.comp (diagonal (H:=H) (κ⊕ι) a)=
      (diagonal (H:=H) ι a).comp (rightCopies (H:=H) ι κ).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (rightCopies_diagonal ι κ (star a))
  simpa only [adjoint_comp,←star_eq_adjoint,←map_star,star_star] using h

lemma rightCopies_commutator_norm
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (rightCopies ι κ) Y*diagonal (H:=H) (κ⊕ι) a-
      diagonal (H:=H) (κ⊕ι) a*extend (rightCopies ι κ) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ :=
  norm_extend_commutator _ _ _ _ (rightCopies_diagonal ι κ a) (rightCopies_adjoint_diagonal ι κ a)

end Kadison.HilbertPadding

end

end
end

end OAI
