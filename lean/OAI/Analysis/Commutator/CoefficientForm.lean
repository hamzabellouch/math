import Mathlib
import OAI.Analysis.Commutator.MultilinearTensors

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.PreHilbert

open UniformSpace Function

abbrev wordSpace (E F : PreHilbert) (n : ℕ) := Completion (E ⊗[ℂ] power F n)

def word (E F : PreHilbert) (n : ℕ) (d : E) (x : Fin n → F) : wordSpace E F n :=
  (d ⊗ₜ[ℂ] pure F n x : E ⊗[ℂ] power F n)

@[simp] lemma norm_word (E F : PreHilbert) (n : ℕ) (d : E) (x : Fin n → F) :
    ‖word E F n d x‖ = ‖d‖ * ∏ i, ‖x i‖ := by
  simp only [word, Completion.norm_coe, TensorProduct.norm_tmul, norm_pure]

@[simp] lemma inner_word (E F : PreHilbert) (n : ℕ) (d e : E) (x y : Fin n → F) :
    inner ℂ (word E F n d x) (word E F n e y) =
      inner ℂ d e * ∏ i, inner ℂ (x i) (y i) := by
  simp only [word, Completion.inner_coe, TensorProduct.inner_tmul, inner_pure]

lemma word_add_left (E F : PreHilbert) (n : ℕ) (d e : E) (x : Fin n → F) :
    word E F n (d + e) x = word E F n d x + word E F n e x := by
  simp only [word, TensorProduct.add_tmul, Completion.coe_add]

lemma word_smul_left (E F : PreHilbert) (n : ℕ) (c : ℂ) (d : E) (x : Fin n → F) :
    word E F n (c • d) x = c • word E F n d x := by
  simp only [word, ← TensorProduct.smul_tmul', Completion.coe_smul]

lemma word_update_add (E F : PreHilbert) (n : ℕ) (d : E) (v : Fin n → F)
    (i : Fin n) (x y : F) :
    word E F n d (update v i (x + y)) =
      word E F n d (update v i x) + word E F n d (update v i y) := by
  simp only [word, pure_update_add, TensorProduct.tmul_add, Completion.coe_add]

lemma word_update_smul (E F : PreHilbert) (n : ℕ) (d : E) (v : Fin n → F)
    (i : Fin n) (c : ℂ) (x : F) :
    word E F n d (update v i (c • x)) = c • word E F n d (update v i x) := by
  simp only [word, pure_update_smul, TensorProduct.tmul_smul, Completion.coe_smul]

end Kadison.PreHilbert
end

end OAI
