import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

structure PreHilbert where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [ipSpace : InnerProductSpace ℂ carrier]

attribute [instance] PreHilbert.normed PreHilbert.ipSpace

instance : CoeSort PreHilbert Type := ⟨PreHilbert.carrier⟩

namespace PreHilbert

abbrev scalar : PreHilbert := ⟨ℂ⟩

abbrev tensor (E F : PreHilbert) : PreHilbert := ⟨E ⊗[ℂ] F⟩

@[reducible] def power (E : PreHilbert) : ℕ → PreHilbert
  | 0 => scalar
  | n + 1 => tensor E (power E n)

def pure (E : PreHilbert) : ∀ n, (Fin n → E) → power E n
  | 0, _ => (1 : ℂ)
  | n + 1, v => v 0 ⊗ₜ[ℂ] pure E n (Fin.tail v)

@[simp] theorem pure_zero (E : PreHilbert) (v : Fin 0 → E) :
    pure E 0 v = (1 : ℂ) := rfl

@[simp] theorem pure_succ (E : PreHilbert) (n : ℕ) (v : Fin (n+1) → E) :
    pure E (n+1) v = v 0 ⊗ₜ[ℂ] pure E n (Fin.tail v) := rfl

@[simp] theorem norm_pure (E : PreHilbert) (n : ℕ) (v : Fin n → E) :
    ‖pure E n v‖ = ∏ i, ‖v i‖ := by
  induction n with
  | zero => simp [pure, power, scalar]
  | succ n ih =>
    rw [pure_succ, TensorProduct.norm_tmul, ih, Fin.prod_univ_succ]
    rfl

@[simp] theorem inner_pure (E : PreHilbert) (n : ℕ) (v w : Fin n → E) :
    inner ℂ (pure E n v) (pure E n w) = ∏ i, inner ℂ (v i) (w i) := by
  induction n with
  | zero => simp [pure, power, scalar]
  | succ n ih =>
    rw [pure_succ, pure_succ, TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]
    rfl

theorem span_pure (E : PreHilbert) (n : ℕ) :
    Submodule.span ℂ (Set.range (pure E n)) = ⊤ := by
  induction n with
  | zero =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (pure E 0)) :=
      Submodule.subset_span ⟨Fin.elim0, rfl⟩
    simpa using (Submodule.span ℂ (Set.range (pure E 0))).smul_mem z h
  | succ n ih =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul x y =>
      have hy : y ∈ Submodule.span ℂ (Set.range (pure E n)) := by rw [ih]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        apply Submodule.subset_span
        exact ⟨Fin.cons x v, by simp [pure]⟩
      | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
      | add y z _ _ hy hz =>
        simpa only [TensorProduct.tmul_add] using
          (Submodule.span ℂ (Set.range (pure E (n+1)))).add_mem hy hz
      | smul c y _ hy =>
        simpa only [TensorProduct.tmul_smul] using
          (Submodule.span ℂ (Set.range (pure E (n+1)))).smul_mem c hy

end PreHilbert

end Kadison
end

end OAI
