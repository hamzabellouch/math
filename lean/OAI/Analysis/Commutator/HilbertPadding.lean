import Mathlib
import OAI.Analysis.Commutator.IsometryCompression
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (E.toContinuousLinearMap.comp T).comp E.toContinuousLinearMap.adjoint

lemma norm_extend_le (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : ‖extend E T‖ ≤ ‖T‖ := by
  have he : ‖E.toContinuousLinearMap‖ ≤ 1 := E.norm_toContinuousLinearMap_le
  have he' : ‖E.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact he
  calc
    _ ≤ ‖E.toContinuousLinearMap‖*‖T‖*‖E.toContinuousLinearMap.adjoint‖ :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*‖T‖*1 := mul_le_mul (mul_le_mul_of_nonneg_right he (norm_nonneg _))
      he' (norm_nonneg _) (by positivity)
    _ = ‖T‖ := by ring

lemma compress_extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    FreeCorner.compress E (extend E T)=T := by
  ext x
  change E.toContinuousLinearMap.adjoint (E (T (E.toContinuousLinearMap.adjoint (E x))))=T x
  simp only [FreeCorner.isometry_adjoint_apply]

lemma norm_extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : ‖extend E T‖=‖T‖ := by
  apply le_antisymm (norm_extend_le E T)
  simpa only [compress_extend] using FreeCorner.norm_compress_le E (extend E T)

lemma extend_commutator (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
    (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
    extend E T*b-b*extend E T=extend E (T*a-a*T) := by
  simp only [extend,mul_def,comp_sub,sub_comp,comp_assoc]
  rw [hr,←comp_assoc b,hl]
  simp only [comp_assoc]

lemma norm_extend_commutator (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
    (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
    ‖extend E T*b-b*extend E T‖=‖T*a-a*T‖ := by
  rw [extend_commutator E T a b hl hr,norm_extend]

open OperatorAmplification

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

def leftCopies : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=H) (ι⊕κ) where
  toFun v := WithLp.toLp 2 (Sum.elim (fun i => v i) (fun _ => 0))
  map_add' v w := by ext i; cases i <;> simp
  map_smul' z v := by ext i; cases i <;> simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]

omit [CompleteSpace H] in
@[simp] lemma leftCopies_inl (v : SumSpace (H:=H) ι) (i : ι) :
    leftCopies ι κ v (Sum.inl i)=v i := rfl

omit [CompleteSpace H] in
@[simp] lemma leftCopies_inr (v : SumSpace (H:=H) ι) (k : κ) :
    leftCopies ι κ v (Sum.inr k)=0 := rfl

local instance : DecidableEq ι := Classical.decEq ι

local instance : DecidableEq κ := Classical.decEq κ

lemma leftCopies_diagonal (a : H →L[ℂ] H) :
    (diagonal (H:=H) (ι⊕κ) a).comp (leftCopies (H:=H) ι κ).toContinuousLinearMap=
      (leftCopies (H:=H) ι κ).toContinuousLinearMap.comp (diagonal (H:=H) ι a) := by
  ext v i
  cases i <;> simp

lemma adjoint_leftCopies_diagonal (a : H →L[ℂ] H) :
    (leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint.comp (diagonal (H:=H) (ι⊕κ) a)=
      (diagonal (H:=H) ι a).comp (leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (leftCopies_diagonal ι κ (star a))
  simpa only [adjoint_comp, ←star_eq_adjoint, ←map_star, star_star] using h

theorem copy_padding_commutator_norm
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (leftCopies ι κ) Y*diagonal (H:=H) (ι⊕κ) a-
      diagonal (H:=H) (ι⊕κ) a*extend (leftCopies ι κ) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ :=
  norm_extend_commutator _ _ _ _ (leftCopies_diagonal ι κ a) (adjoint_leftCopies_diagonal ι κ a)

end Kadison.HilbertPadding

end

end
end

end OAI
