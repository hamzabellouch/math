import Mathlib

namespace OAI

noncomputable section
open scoped MatrixOrder ComplexOrder BigOperators
open Matrix
namespace MatrixPolar

lemma isometry_factor {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (f g : V →ₗ[ℂ] V)
    (hn : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : V →ₗᵢ[ℂ] V, U.toLinearMap.comp g = f := by
  have hk : g.ker ≤ f.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [hn, LinearMap.mem_ker.mp hx, norm_zero]
  let l : g.range →ₗ[ℂ] V :=
    (g.ker.liftQ f hk).comp g.quotKerEquivRange.symm.toLinearMap
  have hl (x : V) : l ⟨g x, LinearMap.mem_range_self g x⟩ = f x := by
    simp [l]
  have hln (x : g.range) : ‖l x‖ = ‖x‖ := by
    rcases x with ⟨x,hx⟩
    obtain ⟨y,rfl⟩ := hx
    rw [hl]
    exact hn y
  let L : g.range →ₗᵢ[ℂ] V := ⟨l,hln⟩
  refine ⟨L.extend,?_⟩
  ext x
  change L.extend (g x) = f x
  rw [show L.extend (g x) = L ⟨g x, LinearMap.mem_range_self g x⟩ from
    L.extend_apply ⟨g x, LinearMap.mem_range_self g x⟩]
  exact hl x

variable {n : Type*} [Fintype n] [DecidableEq n]
lemma gram_inner (A : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) =
      inner ℂ x (Matrix.toEuclideanLin (Aᴴ * A) y) := by
  rw [Matrix.toLpLin_mul 2 2 2, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A) x
    (Matrix.toEuclideanLin A y)).symm

lemma sqrt_gram_norm (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A x‖ =
      ‖Matrix.toEuclideanLin (CFC.sqrt (Aᴴ * A)) x‖ := by
  have h : (CFC.sqrt (Aᴴ * A))ᴴ * CFC.sqrt (Aᴴ * A) = Aᴴ * A := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), gram_inner, gram_inner, h]

lemma polar (A : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ A = U * CFC.sqrt (Aᴴ * A) := by
  obtain ⟨l,hl⟩ := isometry_factor (Matrix.toEuclideanLin A)
    (Matrix.toEuclideanLin (CFC.sqrt (Aᴴ * A))) (sqrt_gram_norm A)
  let U := Matrix.toEuclideanLin.symm l.toLinearMap
  have hU : Matrix.toEuclideanLin U = l.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  refine ⟨U,?_,?_⟩
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      hU, Matrix.toLpLin_one]
    exact l.adjoint_comp_self'
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2, hU]
    exact hl.symm

end MatrixPolar

end

end OAI
