import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexifiedLieAutomorphism

namespace OAI

/-! # Descending a conjugation-invariant complex derivation -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

theorem complexificationRealPart_one_lie (x : L) (y : ℂ ⊗[ℝ] L) :
    complexificationRealPart L ⁅(1 : ℂ) ⊗ₜ[ℝ] x, y⁆ =
      ⁅x, complexificationRealPart L y⁆ := by
  rw [← lie_skew ((1 : ℂ) ⊗ₜ[ℝ] x) y, map_neg,
    complexificationRealPart_lie_one, lie_skew]

def complexDerivationRealPart (D : LieDerivation ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L)) :
    LieDerivation ℝ L L :=
  { toLinearMap := (complexificationRealPart L).comp
      ((D.toLinearMap.restrictScalars ℝ).comp (complexificationLieHom L).toLinearMap)
    leibniz' := by
      intro x y
      change complexificationRealPart L (D ((1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆)) = _
      rw [show (1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆ =
          ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ by simp,
        D.apply_lie_eq_sub, map_sub, complexificationRealPart_one_lie,
        complexificationRealPart_one_lie]
      rfl }

theorem complexDerivationRealPart_embed
    (D : LieDerivation ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L))
    (hc : ∀ z, complexificationConjSemilinear L (D z) =
      D (complexificationConjSemilinear L z)) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] complexDerivationRealPart L D x = D ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  have hf : complexificationConjugation L (D ((1 : ℂ) ⊗ₜ[ℝ] x)) =
      D ((1 : ℂ) ⊗ₜ[ℝ] x) := by
    change complexificationConjSemilinear L (D _) = _
    rw [hc]
    simp [complexificationConjSemilinear]
  obtain ⟨y, hy⟩ := (complexification_conjugation_fixed_iff L _).mp hf
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L (D ((1 : ℂ) ⊗ₜ[ℝ] x)) = _
  rw [hy]
  simp

theorem complexDerivationRealPart_baseChange
    (D : LieDerivation ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L))
    (hc : ∀ z, complexificationConjSemilinear L (D z) =
      D (complexificationConjSemilinear L z)) :
    (complexDerivationRealPart L D).toLinearMap.baseChange ℂ = D.toLinearMap := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul z x =>
    change z ⊗ₜ[ℝ] complexDerivationRealPart L D x = D (z ⊗ₜ[ℝ] x)
    have h := congrArg (fun y : ℂ ⊗[ℝ] L => z • y)
      (complexDerivationRealPart_embed L D hc x)
    simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add v w hv hw => simp only [map_add, hv, hw]

end PolycyclicRecognition

end

end OAI
