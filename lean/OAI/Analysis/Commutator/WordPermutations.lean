import Mathlib
import OAI.Analysis.Commutator.CoefficientForm
import OAI.Analysis.Commutator.TensorActions
import OAI.Analysis.Commutator.TensorPermutations2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.PreHilbert

open UniformSpace

open scoped TensorProduct

def reindexPower (F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l) :
    power F k ≃ₗᵢ[ℂ] power F l :=
  gramEquiv (pure F k) (fun x => pure F l (x ∘ b.symm)) (span_pure F k)
    (by
      have hr : Set.range (fun x => pure F l (x ∘ b.symm)) = Set.range (pure F l) := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨x ∘ b.symm, rfl⟩
        · rintro ⟨y, rfl⟩
          refine ⟨y ∘ b, ?_⟩
          exact congrArg (pure F l) (funext fun i => by simp)
      rw [hr, span_pure])
    (by
      intro x y
      simp only [inner_pure, Function.comp_apply]
      exact Equiv.prod_comp b.symm (fun i => inner ℂ (x i) (y i)))

@[simp] lemma reindexPower_pure (F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l)
    (x : Fin k → F) : reindexPower F b (pure F k x) = pure F l (x ∘ b.symm) :=
  gramEquiv_apply _ _ _ _ _ _

def wordReindex (E F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l) :
    wordSpace E F k →ₗᵢ[ℂ] wordSpace E F l :=
  completionIsometry (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E)
    (reindexPower F b).toLinearIsometry)

@[simp] lemma wordReindex_word (E F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l)
    (d : E) (x : Fin k → F) :
    wordReindex E F b (word E F k d x) = word E F l d (x ∘ b.symm) := by
  simp only [wordReindex, word, completionIsometry_coe, TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
    LinearIsometry.coe_toLinearMap, LinearIsometry.id_apply, LinearIsometryEquiv.coe_toLinearIsometry, reindexPower_pure]

lemma wordReindex_inner (E F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l)
    (d c : E) (x : Fin k → F) (y : Fin l → F) :
    inner ℂ (word E F l c y) (wordReindex E F b (word E F k d x)) =
      inner ℂ c d * ∏ i, inner ℂ (y (b i)) (x i) := by
  rw [wordReindex_word, inner_word]
  congr 1
  simpa using (Equiv.prod_comp b (fun j => inner ℂ (y j) (x (b.symm j)))).symm

end Kadison.PreHilbert
end

end OAI
