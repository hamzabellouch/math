import Mathlib
import OAI.Analysis.MatrixSigning.Potential.CovarianceE

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open scoped BigOperators
open Matrix

local instance : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {m : ℕ}

lemma quad_gram (C : Mat m) (x : E m) :
    quad (C.conjTranspose * C) x = inner ℝ (C.toEuclideanLin x) (C.toEuclideanLin x) := by
  simp only [quad,toEuclideanLin_mul,LinearMap.comp_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

theorem exists_singular_subspace (C : Mat m) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : Submodule ℝ (E m),
      (m : ℝ) - (C.conjTranspose*C).trace / ρ ≤ Module.finrank ℝ G ∧
      ∀ x ∈ G, inner ℝ (C.toEuclideanLin x) (C.toEuclideanLin x) ≤ ρ * inner ℝ x x := by
  classical
  have hC := Matrix.posSemidef_conjTranspose_mul_self C
  let F := highCoordinates hC.isHermitian ρ
  refine ⟨F.ker,?_,?_⟩
  · have hd := finrank_inf_ker_add (⊤ : Submodule ℝ (E m)) F
    have he : (⊤ : Submodule ℝ (E m)) ⊓ F.ker = F.ker := top_inf_eq _
    rw [he] at hd
    simp only [finrank_top,finrank_euclideanSpace,Fintype.card_fin] at hd
    have hcount := high_count_mul_le_trace hC ρ
    have hd' : (m : ℝ) ≤ (Module.finrank ℝ F.ker : ℝ) + Fintype.card (High hC.isHermitian ρ) := by
      exact_mod_cast hd
    have hcount' := (le_div_iff₀ hρ).mpr hcount
    linarith
  · intro x hx
    rw [← quad_gram]
    apply low_eigen_quad_le hC.isHermitian
    intro i hi
    have hh := congrFun hx (⟨i,hi⟩ : High hC.isHermitian ρ)
    exact hh

lemma gram_trace (C : Mat m) : (C.conjTranspose*C).trace = ∑ i, ∑ j, (C i j)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

open scoped BigOperators
open Matrix

local instance : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {m n : ℕ}

lemma weighted_singular_subspace (C : Mat m) (W : E m ≃ₗ[ℝ] E m) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : Submodule ℝ (E m),
      (m : ℝ) - (C.conjTranspose*C).trace / ρ ≤ Module.finrank ℝ G ∧
      ∀ x ∈ G, inner ℝ (C.toEuclideanLin (W x)) (C.toEuclideanLin (W x)) ≤
        ρ * inner ℝ (W x) (W x) := by
  obtain ⟨G,hG,hq⟩ := exists_singular_subspace C hρ
  refine ⟨G.map W.symm.toLinearMap,?_,?_⟩
  · rw [LinearEquiv.finrank_map_eq W.symm G]
    exact hG
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hq y hy

lemma coupled_singular_subspace (C : Mat m) (W : E m ≃ₗ[ℝ] E m)
    (L : E m →ₗ[ℝ] E n) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : Submodule ℝ (E m),
      (m : ℝ) - (C.conjTranspose*C).trace / ρ - n ≤ Module.finrank ℝ G ∧
      (∀ x ∈ G, L x = 0) ∧
      ∀ x ∈ G, inner ℝ (C.toEuclideanLin (W x)) (C.toEuclideanLin (W x)) ≤
        ρ * inner ℝ (W x) (W x) := by
  obtain ⟨G,hG,hq⟩ := weighted_singular_subspace C W hρ
  refine ⟨G ⊓ L.ker,?_,fun x hx => hx.2,fun x hx => hq x hx.1⟩
  have hd : Module.finrank ℝ G ≤ Module.finrank ℝ (G ⊓ L.ker : Submodule ℝ (E m)) + n := by
    have hr := L.finrank_range_add_finrank_ker
    have hi := G.finrank_sup_add_finrank_inf_eq L.ker
    have hs := Submodule.finrank_le (G ⊔ L.ker)
    have hf := Submodule.finrank_le L.range
    simp only [finrank_euclideanSpace,Fintype.card_fin] at *
    omega
  have hd' : (Module.finrank ℝ G : ℝ) ≤ Module.finrank ℝ (G ⊓ L.ker : Submodule ℝ (E m)) + n := by
    exact_mod_cast hd
  linarith

theorem coupled_covariance (C : Mat (2*n)) (W : E (2*n) ≃ₗ[ℝ] E (2*n))
    (L : E (2*n) →ₗ[ℝ] E n)
    (htr : (C.conjTranspose*C).trace ≤ (2*n : ℝ)/384) :
    ∃ Γ : Mat (2*n), Γ.PosSemidef ∧
      (∀ i, Γ i i ≤ 1) ∧ (slack 4 Γ).PosSemidef ∧
      (23/48 : ℝ)*n ≤ Γ.trace ∧
      (∀ x, L (Γ.toEuclideanLin x) = 0) ∧
      ∀ x, inner ℝ (C.toEuclideanLin (W (Γ.toEuclideanLin x)))
          (C.toEuclideanLin (W (Γ.toEuclideanLin x))) ≤
        (1/4 : ℝ)*inner ℝ (W (Γ.toEuclideanLin x)) (W (Γ.toEuclideanLin x)) := by
  obtain ⟨G,hG,hL,hq⟩ := coupled_singular_subspace C W L (by norm_num : (0 : ℝ) < 1/4)
  have hd : (1/(4 : ℝ)+23/96)*(2*n : ℝ) ≤ Module.finrank ℝ G := by
    push_cast at hG
    linarith
  obtain ⟨Γ,hΓ,hsupp,hdiag,hslack,ht⟩ := subspace_covariance G
    (by norm_num : (1 : ℝ) < 4) (by norm_num : (0 : ℝ) < 23/96) (by simpa using hd)
  refine ⟨Γ,hΓ,hdiag,hslack,?_,fun x => hL _ (hsupp x),fun x => hq _ (hsupp x)⟩
  push_cast at ht
  linarith

end CurrentKS.Covariance

end

end OAI
