import Mathlib
import OAI.Analysis.Commutator.CoefficientForm

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

open UniformSpace TensorProduct

@[fun_prop] lemma continuous_pure (E : PreHilbert) (n : ℕ) :
    Continuous (pure E n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun x : Fin (n+1) → E => x 0 ⊗ₜ[ℂ] pure E n (Fin.tail x))
    have ht : Continuous (fun x : Fin (n+1) → E => Fin.tail x) :=
      continuous_pi (fun i => continuous_apply i.succ)
    exact (TensorProduct.continuous_tmul (𝕜 := ℂ) (E := E) (F := power E n)).comp
      ((continuous_apply (0 : Fin (n+1))).prodMk (ih.comp ht))

@[fun_prop] lemma continuous_word (E F : PreHilbert) (n : ℕ) :
    Continuous (fun z : E × (Fin n → F) => word E F n z.1 z.2) := by
  unfold word
  exact (Completion.continuous_coe (E ⊗[ℂ] power F n)).comp
    ((TensorProduct.continuous_tmul (𝕜 := ℂ) (E := E) (F := power F n)).comp
    (continuous_fst.prodMk ((continuous_pure F n).comp continuous_snd)))

lemma eq_zero_of_word_inner (E F : PreHilbert) (n : ℕ) (z : wordSpace E F n)
    (hz : ∀ d x, inner ℂ (word E F n d x) z = 0) : z = 0 := by
  apply Completion.denseRange_coe.eq_zero_of_inner_right ℂ
  intro a
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp [Completion.coe_add, inner_add_left, ha, hb]
  | tmul d x =>
    have hx : x ∈ Submodule.span ℂ (Set.range (pure F n)) := by
      rw [span_pure]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact hz d v
    | zero => simp only [TensorProduct.tmul_zero, Completion.coe_zero, inner_zero_left]
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, Completion.coe_add, inner_add_left, hx, hy]
    | smul c x _ hx => simp only [TensorProduct.tmul_smul, Completion.coe_smul, inner_smul_left, hx, mul_zero]

lemma continuousLinearMap_ext_word (E F : PreHilbert) (n : ℕ) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T U : wordSpace E F n →L[ℂ] G)
    (h : ∀ d x, T (word E F n d x) = U (word E F n d x)) : T = U := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [Completion.coe_add, map_add, ha, hb]
    | tmul d x =>
      have hx : x ∈ Submodule.span ℂ (Set.range (pure F n)) := by
        rw [span_pure]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        exact h d v
      | zero => simp only [TensorProduct.tmul_zero, Completion.coe_zero, map_zero]
      | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, Completion.coe_add, map_add, hx, hy]
      | smul c x _ hx => simp only [TensorProduct.tmul_smul, Completion.coe_smul, map_smul, hx]

lemma continuousLinearMap_ext_word_inner (E F : PreHilbert) (k l : ℕ)
    (T U : wordSpace E F k →L[ℂ] wordSpace E F l)
    (h : ∀ d x c y, inner ℂ (word E F l c y) (T (word E F k d x)) =
      inner ℂ (word E F l c y) (U (word E F k d x))) : T = U := by
  apply continuousLinearMap_ext_word E F k T U
  intro d x
  apply sub_eq_zero.mp
  apply eq_zero_of_word_inner E F l
  intro c y
  rw [inner_sub_right, h, sub_self]

end Kadison.PreHilbert
end

end OAI
