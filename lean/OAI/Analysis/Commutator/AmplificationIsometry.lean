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

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type*) [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

def amplifyIsometry (E : H →ₗᵢ[ℂ] K) : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=K) ι where
  toFun v := WithLp.toLp 2 (fun i => E (v i))
  map_add' v w := by ext i; simp
  map_smul' z v := by ext i; simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2]

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma amplifyIsometry_apply (E : H →ₗᵢ[ℂ] K) (v : SumSpace (H:=H) ι) (i : ι) :
    amplifyIsometry ι E v i=E (v i) := rfl

lemma amplifyIsometry_adjoint (E : H →ₗᵢ[ℂ] K) (v : SumSpace (H:=K) ι) :
    (amplifyIsometry ι E).toContinuousLinearMap.adjoint v=
      WithLp.toLp 2 (fun i => E.toContinuousLinearMap.adjoint (v i)) := by
  apply ext_inner_left ℂ
  intro w
  rw [adjoint_inner_right]
  simp only [PiLp.inner_apply,amplifyIsometry_apply,adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap]

lemma diagonal_extend (E : H →ₗᵢ[ℂ] K) (Y : H →L[ℂ] H) :
    diagonal (H:=K) ι (extend E Y)=extend (amplifyIsometry ι E) (diagonal (H:=H) ι Y) := by
  ext v i
  simp [extend,amplifyIsometry_adjoint]

lemma amplifyIsometry_matrix_intertwines (E : H →ₗᵢ[ℂ] K)
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hE : ∀ a,(σ a).comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (ρ a))
    (X : CStarMatrix ι ι A) :
    (matrixRepresentation σ X).comp (amplifyIsometry ι E).toContinuousLinearMap=
      (amplifyIsometry ι E).toContinuousLinearMap.comp (matrixRepresentation ρ X) := by
  ext v i
  change matrixAction (fun i j => σ (X i j)) (amplifyIsometry ι E v) i=
    E (matrixAction (fun i j => ρ (X i j)) v i)
  simp only [matrixAction_apply,amplifyIsometry_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun T : H →L[ℂ] K => T (v j)) (hE (X i j))

lemma amplifyIsometry_adjoint_matrix_intertwines (E : H →ₗᵢ[ℂ] K)
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hE : ∀ a,(σ a).comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (ρ a))
    (X : CStarMatrix ι ι A) :
    (amplifyIsometry ι E).toContinuousLinearMap.adjoint.comp (matrixRepresentation σ X)=
      (matrixRepresentation ρ X).comp (amplifyIsometry ι E).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (amplifyIsometry_matrix_intertwines ι E ρ σ hE (star X))
  simpa only [adjoint_comp,←star_eq_adjoint,←map_star,star_star] using h

theorem amplified_extension_commutator_norm (E : H →ₗᵢ[ℂ] K)
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hE : ∀ a,(σ a).comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp (ρ a))
    (Y : H →L[ℂ] H) (X : CStarMatrix ι ι A) :
    ‖diagonal (H:=K) ι (extend E Y)*matrixRepresentation σ X-
      matrixRepresentation σ X*diagonal (H:=K) ι (extend E Y)‖=
    ‖diagonal (H:=H) ι Y*matrixRepresentation ρ X-
      matrixRepresentation ρ X*diagonal (H:=H) ι Y‖ := by
  rw [diagonal_extend]
  exact norm_extend_commutator _ _ _ _ (amplifyIsometry_matrix_intertwines ι E ρ σ hE X)
    (amplifyIsometry_adjoint_matrix_intertwines ι E ρ σ hE X)

end Kadison.HilbertPadding

end

end
end

end OAI
