import OAI.Analysis.Pureness.GroupAlgebra.WordShellFactorization
import OAI.Analysis.Pureness.Tensor.SpatialSchurBounded
import OAI.Analysis.Pureness.Tensor.SpatialSymbolMultiplier

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace TensorProduct
local instance spatialFreeGroupShellDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {A H X : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def freeGroupShellSymbol (n : ℕ) (g : FreeGroup X) : ℂ :=
  if g.toWord.length = n then 1 else 0

include hα in

theorem spatialFreeGroupShell_polynomial_bound (n : ℕ) (a : FreeGroup X →₀ A) :
    ‖spatialGroupPolynomialMap (G := FreeGroup X) α (groupPolynomialWeight (freeGroupShellSymbol n) a)‖ ≤
      (3 * (n : ℝ) + 2) ^ 2 * ‖spatialGroupPolynomialMap (G := FreeGroup X) α a‖ := by
  change ‖(spatialGroupPolynomialMap (G := FreeGroup X) α (groupPolynomialWeight (freeGroupShellSymbol n) a)).val‖ ≤
    (3 * (n : ℝ) + 2) ^ 2 * ‖(spatialGroupPolynomialMap (G := FreeGroup X) α a).val‖
  have hb := spatialSchur_norm_le_fintype_sum (wordShellSign n) (wordShellSign_norm n)
    (fun i (g : FreeGroup X) => wordShellLeft n i g⁻¹.toWord)
    (fun i (g : FreeGroup X) => wordShellRight n i g⁻¹.toWord)
    (fun i g => wordShellLeft_norm n i g⁻¹.toWord)
    (fun i g => wordShellRight_norm n i g⁻¹.toWord)
    (spatialGroupPolynomialMap (G := FreeGroup X) α (groupPolynomialWeight (freeGroupShellSymbol n) a)).val
    (spatialGroupPolynomialMap (G := FreeGroup X) α a).val ?_
  · apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (ContinuousLinearMap.opNorm_nonneg
      (spatialGroupPolynomialMap (G := FreeGroup X) α a).val)
    have hn : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    have hc : (Fintype.card (WordShellIndex n) : ℝ) = (n : ℝ) + 1 + 2 * ((n - 1 : ℕ) : ℝ) := by
      simp [WordShellIndex, Fintype.card_sum, Nat.cast_add]; ring
    rw [hc]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro g h
    refine (spatialGroupPolynomialMap_compression α hα
      (groupPolynomialWeight (freeGroupShellSymbol n) a) g h).symm.trans ?_
    have hk : freeGroupShellSymbol n (g*h⁻¹) =
        ∑ i : WordShellIndex n, wordShellSign n i *
          ⟪wordShellLeft n i g⁻¹.toWord, wordShellRight n i h⁻¹.toWord⟫_ℂ := by
      rw [freeGroupShellSymbol, freeGroup_mul_inv_length]
      exact wordShell_factorization n _ _
    calc
      _ = α (freeGroupShellSymbol n (g*h⁻¹) • a (g*h⁻¹)) :=
        congrArg α (groupPolynomialWeight_apply (freeGroupShellSymbol n) a (g*h⁻¹))
      _ = freeGroupShellSymbol n (g*h⁻¹) • α (a (g*h⁻¹)) := map_smul α _ _
      _ = _ := congrArg₂ (fun (z : ℂ) (T : H →L[ℂ] H) => z • T)
        hk (spatialGroupPolynomialMap_compression α hα a g h)

def spatialFreeGroupShell (n : ℕ) :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype :=
  spatialSymbolMultiplier α (freeGroupShellSymbol n)

include hα in
theorem spatialFreeGroupShell_norm_le (n : ℕ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup X)).subtype) :
    ‖spatialFreeGroupShell (X := X) α n x‖ ≤ (3 * (n : ℝ) + 2) ^ 2 * ‖x‖ :=
  spatialSymbolMultiplier_norm_le α _ _ (spatialFreeGroupShell_polynomial_bound α hα n) x

include hα in
lemma spatialFreeGroupShell_opNorm_le (n : ℕ) :
    ‖spatialFreeGroupShell (X := X) α n‖ ≤ (3 * (n : ℝ) + 2) ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
    (spatialFreeGroupShell_norm_le α hα n)

include hα in
lemma spatialFreeGroupShell_generator (n : ℕ) (a : A) (g : FreeGroup X) :
    spatialFreeGroupShell (X := X) α n
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X)))) =
    freeGroupShellSymbol n g •
      spatialCompletionMap α (reducedGroupAlgebra (FreeGroup X)).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup X) g : reducedGroupAlgebra (FreeGroup X))) :=
  spatialSymbolMultiplier_generator α _ _ (spatialFreeGroupShell_polynomial_bound α hα n) a g
end CuntzPureness

end

end OAI
