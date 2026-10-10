import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Pull

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma update_pair_swap {N : ℕ} {C : Type*} (f : Fin N → C) (i j : Fin N) (u : C) :
    Function.update (Function.update (f ∘ Equiv.swap i j) j u) i u =
      Function.update (Function.update f j u) i u := by
  classical
  ext k
  by_cases hki : k = i
  · subst k; simp
  by_cases hkj : k = j
  · rw [hkj] at hki ⊢
    simp only [Function.update_of_ne hki, Function.update_self]
  simp [Function.update_of_ne hki, Function.update_of_ne hkj,
    Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

lemma project_pair_swap {N : ℕ} (i j : Fin (N+1)) (hij : i ≠ j) (u : Lp ℂ 2 μ) :
    ((projectOrbital i u).comp (projectOrbital j u)).comp (permute (Equiv.swap i j)) =
      (projectOrbital i u).comp (projectOrbital j u) := by
  classical
  apply continuousLinearMap_ext_pure
  intro f
  simp only [ContinuousLinearMap.comp_apply, permute_pure, Equiv.symm_swap,
    projectOrbital_pure, map_smul, Function.update_of_ne hij, smul_smul,
    Function.comp_apply, Equiv.swap_apply_right, Equiv.swap_apply_left, update_pair_swap,
    mul_comm]

lemma project_pair_eq_zero {N : ℕ} (i j : Fin (N+1)) (hij : i ≠ j)
    (u : Lp ℂ 2 μ) (ψ : sectorL2 (N+1) μ) (hψ : permute (Equiv.swap i j) ψ = -ψ) :
    projectOrbital i u (projectOrbital j u ψ) = 0 := by
  have he := congrArg (fun F : sectorL2 (N+1) μ →L[ℂ] sectorL2 (N+1) μ => F ψ)
    (project_pair_swap i j hij u)
  simp only [ContinuousLinearMap.comp_apply, hψ, map_neg] at he
  have hi := congrArg (fun w => ⟪projectOrbital i u (projectOrbital j u ψ), w⟫_ℂ) he
  rw [inner_neg_right] at hi
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  linear_combination (norm := ring_nf) -(1/2 : ℂ) * hi

lemma project_inner {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) (ψ φ : sectorL2 (N+1) μ) :
    ⟪projectOrbital i u ψ, φ⟫_ℂ = ⟪ψ, projectOrbital i u φ⟫_ℂ := by
  simp only [projectOrbital, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_adjoint]

lemma project_pair_orthogonal {N : ℕ} (i j : Fin (N+1)) (hij : i ≠ j)
    (u : Lp ℂ 2 μ) (ψ : sectorL2 (N+1) μ) (hψ : permute (Equiv.swap i j) ψ = -ψ) :
    ⟪projectOrbital i u ψ, projectOrbital j u ψ⟫_ℂ = 0 := by
  rw [project_inner, project_pair_eq_zero i j hij u ψ hψ, inner_zero_right]

lemma insertOrbital_norm {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) (ψ : sectorL2 N μ) :
    ‖insertOrbital i u ψ‖ = ‖u‖ * ‖ψ‖ := by
  rw [insertOrbital, ContinuousLinearMap.comp_apply, pull_norm, tensorLeft_apply, tensor_norm]

lemma project_inner_self {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (hu : ‖u‖ = 1) (ψ : sectorL2 (N+1) μ) :
    (⟪projectOrbital i u ψ, ψ⟫_ℂ).re = ‖projectOrbital i u ψ‖^2 := by
  change (⟪insertOrbital i u ((insertOrbital i u).adjoint ψ), ψ⟫_ℂ).re =
    ‖insertOrbital i u ((insertOrbital i u).adjoint ψ)‖^2
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change RCLike.re ⟪(insertOrbital i u).adjoint ψ, (insertOrbital i u).adjoint ψ⟫_ℂ = _
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), insertOrbital_norm, hu, one_mul]

lemma project_norm_equal {N : ℕ} (i j : Fin (N+1)) (u : Lp ℂ 2 μ)
    (ψ : sectorL2 (N+1) μ) (hψ : permute (Equiv.swap i j) ψ = -ψ) :
    ‖projectOrbital i u ψ‖ = ‖projectOrbital j u ψ‖ := by
  have he := congrArg (fun F : sectorL2 (N+1) μ →L[ℂ] sectorL2 (N+1) μ => F ψ)
    (projectOrbital_covariance i u (Equiv.swap i j))
  simp only [ContinuousLinearMap.comp_apply, hψ, Equiv.swap_apply_left, map_neg] at he
  have hn := congrArg norm he
  simpa only [permute_norm, norm_neg] using hn

lemma sum_project_norm_sq_le {N : ℕ} (u : Lp ℂ 2 μ) (hu : ‖u‖ = 1)
    (ψ : sectorL2 (N+1) μ)
    (hψ : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (∑ i : Fin (N+1), ‖projectOrbital i u ψ‖^2) ≤ ‖ψ‖^2 := by
  classical
  let p : Fin (N+1) → sectorL2 (N+1) μ := fun i => projectOrbital i u ψ
  have horth (i j : Fin (N+1)) (hij : i ≠ j) : ⟪p i,p j⟫_ℂ = 0 :=
    project_pair_orthogonal i j hij u ψ (hψ i j hij)
  have hs : ‖∑ i, p i‖^2 = ∑ i, ‖p i‖^2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have he : ⟪∑ i, p i, ∑ j, p j⟫_ℂ = ∑ i, ⟪p i,p i⟫_ℂ := by
      simp only [sum_inner, inner_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_eq_single i (fun j _ hji => horth j i hji) (by simp)
    rw [he, map_sum]
    simp only [inner_self_eq_norm_sq (𝕜 := ℂ)]
  have hp : (⟪∑ i, p i, ψ⟫_ℂ).re = ∑ i, ‖p i‖^2 := by
    rw [sum_inner, Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => project_inner_self i u hu ψ)
  have hn := sq_nonneg ‖(∑ i, p i) - ψ‖
  rw [norm_sub_sq (𝕜 := ℂ), hs] at hn
  change 0 ≤ _ - 2 * (⟪∑ i, p i, ψ⟫_ℂ).re + _ at hn
  rw [hp] at hn
  dsimp only [p] at *
  linarith

lemma occupation_le_one {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) (hu : ‖u‖ = 1)
    (ψ : sectorL2 (N+1) μ)
    (hψ : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (N+1 : ℝ) * ‖(insertOrbital i u).adjoint ψ‖^2 ≤ ‖ψ‖^2 := by
  have hb := sum_project_norm_sq_le u hu ψ hψ
  have hn (j : Fin (N+1)) : ‖projectOrbital j u ψ‖ = ‖(insertOrbital i u).adjoint ψ‖ := by
    have he : ‖projectOrbital j u ψ‖ = ‖projectOrbital i u ψ‖ := by
      by_cases hji : j = i
      · rw [hji]
      exact project_norm_equal j i u ψ (hψ j i hji)
    rw [he]
    change ‖insertOrbital i u ((insertOrbital i u).adjoint ψ)‖ = _
    rw [insertOrbital_norm, hu, one_mul]
  simpa only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] using hb

end CoulombPauli

end

end OAI
