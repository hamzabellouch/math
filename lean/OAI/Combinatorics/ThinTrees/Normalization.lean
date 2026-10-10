import OAI.Combinatorics.ThinTrees.Representation

namespace OAI

universe uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {D : Type uD} [Fintype D] [DecidableEq D]
omit [DecidableEq D] in
lemma symmetric_transform_dot (M : Matrix D D ℝ) (hM : Mᵀ=M) (x y : D → ℝ) :
    x ⬝ᵥ (M *ᵥ y)=(M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec,←mulVec_transpose,hM]
omit [DecidableEq D] in
lemma qform_square (S : Matrix D D ℝ) (hS : Sᵀ=S) (x : D → ℝ) :
    qform (S*S) x=(S*ᵥx) ⬝ᵥ (S*ᵥx) := by
  rw [qform,←mulVec_mulVec,symmetric_transform_dot S hS]
namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_le_base : G.laplacian univ ≤ G.baseMatrix := by
  apply le_add_of_nonneg_right
  exact (Matrix.PosSemidef.one.smul (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)).nonneg

lemma normalized_vectors (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ G.matrixDomain) (B : Finset (Fin m)) :
    ∃a : Fin m → Fin n → ℝ,
      (∀x : Fin n → ℝ, (∑e ∈ B, (x ⬝ᵥ a e)^2) ≤ x ⬝ᵥ x) ∧
      (∀e, a e ⬝ᵥ a e=G.resistance X e) ∧
      (∀v : Fin n → ℝ, ∃x : Fin n → ℝ, x ⬝ᵥ x=qform X v ∧
        ∀e, x ⬝ᵥ a e=v ⬝ᵥ G.incidence e) := by
  classical
  obtain ⟨S,hSH,hSU,hSS⟩ := posDef_sqrt_factors (G.domain_pd hn hX)
  let M := S⁻¹
  have hST : Sᵀ=S := by simpa only [conjTranspose_eq_transpose_of_trivial] using hSH.eq
  have hMT : Mᵀ=M := by simpa only [M,conjTranspose_eq_transpose_of_trivial] using hSH.inv.eq
  have hMS : M*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hSM : S*M=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hMM : M*M=X⁻¹ := by
    apply Eq.symm
    apply Matrix.inv_eq_left_inv
    rw [←hSS,mul_assoc,←mul_assoc M S S,hMS,one_mul,hMS]
  let a : Fin m → Fin n → ℝ := fun e => M*ᵥG.incidence e
  refine ⟨a,?_,?_,?_⟩
  · intro x
    have he : ∀e, x ⬝ᵥ a e=(M*ᵥx) ⬝ᵥ G.incidence e := fun e => symmetric_transform_dot M hMT x _
    simp_rw [he]
    have hb : (∑e ∈ B, ((M*ᵥx) ⬝ᵥ G.incidence e)^2) ≤
        ∑e : Fin m, ((M*ᵥx) ⬝ᵥ G.incidence e)^2 := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => sq_nonneg _)
    have heL : (∑e : Fin m, ((M*ᵥx) ⬝ᵥ G.incidence e)^2)=qform (G.laplacian univ) (M*ᵥx) := by
      rw [G.laplacian_qform]
      apply sum_congr rfl
      intro e _
      congr 1
      exact G.eval_incidence (M*ᵥx) e
    rw [heL] at hb
    have hh := hb.trans (qform_mono (G.laplacian_le_base.trans hX.1) (M*ᵥx))
    rw [←hSS,qform_square S hST,mulVec_mulVec,hSM,one_mulVec] at hh
    exact hh
  · intro e
    change (M*ᵥG.incidence e) ⬝ᵥ (M*ᵥG.incidence e)=qform X⁻¹ (G.incidence e)
    rw [←hMM,qform_square M hMT]
  · intro v
    refine ⟨S*ᵥv,?_,?_⟩
    · rw [←hSS,qform_square S hST]
    · intro e
      change (S*ᵥv) ⬝ᵥ (M*ᵥG.incidence e)=_
      rw [symmetric_transform_dot M hMT,mulVec_mulVec,hMS,one_mulVec]
end MultiGraph
end StrongThinTree

end
end

end OAI
