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

variable (ι : Type*) [Fintype ι]

local instance doubleCopiesIndexDecidableEq : DecidableEq ι := Classical.decEq ι

def doubleCopies : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=H) ((Fin 2)×ι) where
  toFun v := WithLp.toLp 2 (fun p => if p.1=0 then v p.2 else 0)
  map_add' v w := by ext p; by_cases h : p.1=0 <;> simp [h]
  map_smul' z v := by ext p; by_cases h : p.1=0 <;> simp [h]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,Fin.sum_univ_two]

omit [CompleteSpace H] in
@[simp] lemma doubleCopies_apply (v : SumSpace (H:=H) ι) (p : (Fin 2)×ι) :
    doubleCopies ι v p=if p.1=0 then v p.2 else 0 := rfl

lemma doubleCopies_diagonal (a : H →L[ℂ] H) :
    (diagonal (H:=H) ((Fin 2)×ι) a).comp (doubleCopies (H:=H) ι).toContinuousLinearMap=
      (doubleCopies (H:=H) ι).toContinuousLinearMap.comp (diagonal (H:=H) ι a) := by
  ext v p
  simp only [comp_apply,diagonal_apply,LinearIsometry.coe_toContinuousLinearMap,doubleCopies_apply]
  by_cases h : p.1=0 <;> simp [h]

lemma doubleCopies_adjoint_diagonal (a : H →L[ℂ] H) :
    (doubleCopies (H:=H) ι).toContinuousLinearMap.adjoint.comp (diagonal (H:=H) ((Fin 2)×ι) a)=
      (diagonal (H:=H) ι a).comp (doubleCopies (H:=H) ι).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (doubleCopies_diagonal ι (star a))
  simpa only [adjoint_comp,←star_eq_adjoint,←map_star,star_star] using h

theorem doubleCopies_commutator_norm
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (doubleCopies ι) Y*diagonal (H:=H) ((Fin 2)×ι) a-
      diagonal (H:=H) ((Fin 2)×ι) a*extend (doubleCopies ι) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ :=
  norm_extend_commutator _ _ _ _ (doubleCopies_diagonal ι a) (doubleCopies_adjoint_diagonal ι a)

end Kadison.HilbertPadding

end

end
end

end OAI
