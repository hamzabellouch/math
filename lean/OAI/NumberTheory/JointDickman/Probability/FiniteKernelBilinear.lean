import OAI.NumberTheory.JointDickman.Probability.FiniteChannels

namespace OAI

/-! # Bilinear stability of a finite kernel under square-norm approximation -/

namespace JointDickman
open Finset

noncomputable def finiteKernelBilinear {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (u v : A → ℝ) : ℝ :=
  ∑ a, μ a*u a*finiteKernelAction μ K v a

theorem finiteKernelBilinear_bound {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v : A → ℝ) :
    |finiteKernelBilinear μ K u v| ≤
      C*Real.sqrt (∑ a, μ a*u a^2)*Real.sqrt (∑ a, μ a*v a^2) := by
  have hu : 0 ≤ ∑ a, μ a*u a^2 := sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hv : 0 ≤ ∑ a, μ a*v a^2 := sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hs : finiteKernelBilinear μ K u v ^ 2 ≤
      (∑ a, μ a*u a^2)*(∑ a, μ a*finiteKernelAction μ K v a^2) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro a _
      exact mul_nonneg (hμ a) (sq_nonneg _)
    · intro a _
      exact mul_nonneg (hμ a) (sq_nonneg _)
    · intro a _
      ring_nf
      exact le_rfl
  have haction := finiteKernelAction_square_bound μ K hμ hC hrow hcol v
  have hh := hs.trans (mul_le_mul_of_nonneg_left haction hu)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt hu,Real.sq_sqrt hv]
  exact hh.trans_eq (by ring)

theorem finiteKernelBilinear_bound_of_energies {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v : A → ℝ)
    {U V : ℝ} (hu : (∑ a, μ a*u a^2) ≤ U) (hv : (∑ a, μ a*v a^2) ≤ V) :
    |finiteKernelBilinear μ K u v| ≤ C*Real.sqrt U*Real.sqrt V := by
  apply (finiteKernelBilinear_bound μ K hμ hC hrow hcol u v).trans
  gcongr

theorem finiteKernelBilinear_sub {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (u v s t : A → ℝ) :
    finiteKernelBilinear μ K u v-finiteKernelBilinear μ K s t =
      finiteKernelBilinear μ K (fun a => u a-s a) v+
        finiteKernelBilinear μ K s (fun a => v a-t a) := by
  simp only [finiteKernelBilinear,finiteKernelAction,mul_sum,mul_sub,sub_mul,
    sum_sub_distrib]
  ring

theorem finiteKernelBilinear_stability {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v s t : A → ℝ)
    {e₁ e₂ U V : ℝ}
    (he₁ : (∑ a, μ a*(u a-s a)^2) ≤ e₁)
    (he₂ : (∑ a, μ a*(v a-t a)^2) ≤ e₂)
    (hU : (∑ a, μ a*s a^2) ≤ U) (hV : (∑ a, μ a*v a^2) ≤ V) :
    |finiteKernelBilinear μ K u v-finiteKernelBilinear μ K s t| ≤
      C*(Real.sqrt e₁*Real.sqrt V+Real.sqrt U*Real.sqrt e₂) := by
  rw [finiteKernelBilinear_sub]
  exact (abs_add_le _ _).trans ((add_le_add
    (finiteKernelBilinear_bound_of_energies μ K hμ hC hrow hcol _ _ he₁ hV)
    (finiteKernelBilinear_bound_of_energies μ K hμ hC hrow hcol _ _ hU he₂)).trans_eq (by ring))

end JointDickman

end OAI
