import Mathlib

namespace OAI

/-! Gram Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
theorem adjoint_mulVec_mem_gram_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix ι κ ℂ) (x : ι → ℂ) :
    ∃ y : κ → ℂ, (Wᴴ * W) *ᵥ y = Wᴴ *ᵥ x := by
  classical
  have hx : (WithLp.toLp 2 (Wᴴ *ᵥ x)) ∈ W.toEuclideanLin.adjoint.range := by
    refine ⟨WithLp.toLp 2 x, ?_⟩
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.toLpLin_apply]
  rw [← LinearMap.range_adjoint_comp_self] at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨y.ofLp, ?_⟩
  have := congrArg WithLp.ofLp hy
  simpa only [LinearMap.comp_apply, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec] using this

theorem sandwich_quadratic_form {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (C : Matrix ι ι ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ (Aᴴ * C * A) *ᵥ x = star (A *ᵥ x) ⬝ᵥ C *ᵥ (A *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

 
theorem gram_compression_posSemidef_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) (hC : C.IsHermitian) :
    ((Wᴴ * W) * C * (Wᴴ * W)).PosSemidef ↔ (W * C * Wᴴ).PosSemidef := by
  classical
  let G := Wᴴ * W
  have hg : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  constructor
  · intro h
    have h' : (Gᴴ * C * G).PosSemidef := by rwa [hg.eq]
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · change (W * C * Wᴴ)ᴴ = W * C * Wᴴ
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC.eq,
        Matrix.mul_assoc]
    · intro x
      obtain ⟨y, hy⟩ := adjoint_mulVec_mem_gram_range W x
      have hn := h'.dotProduct_mulVec_nonneg y
      rw [sandwich_quadratic_form] at hn
      change 0 ≤ star ((Wᴴ * W) *ᵥ y) ⬝ᵥ C *ᵥ ((Wᴴ * W) *ᵥ y) at hn
      rw [hy] at hn
      rwa [← sandwich_quadratic_form, Matrix.conjTranspose_conjTranspose] at hn
  · intro h
    have := h.conjTranspose_mul_mul_same W
    simpa only [Matrix.mul_assoc] using this
end LaughlinFock
end

end OAI
