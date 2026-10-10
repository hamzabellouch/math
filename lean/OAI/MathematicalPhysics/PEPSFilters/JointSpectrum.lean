import Mathlib

namespace OAI

/-! Joint eigenbases and simultaneous diagonal functional calculus. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter

def JointEigenSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E →ₗ[ℂ] E) (c : Module.End.Eigenvalues B × Module.End.Eigenvalues A) :
    Submodule ℂ E := Module.End.eigenspace A c.2.val ⊓ Module.End.eigenspace B c.1.val

lemma jointEigenSpace_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily ℂ (fun c => JointEigenSpace A B c)
      (fun c => (JointEigenSpace A B c).subtypeₗᵢ) := by
  let f : Module.End.Eigenvalues B × Module.End.Eigenvalues A → ℂ × ℂ := fun c => (c.1.val, c.2.val)
  have hf : Function.Injective f := by
    intro c d h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  intro i j hij x y
  exact hA.orthogonalFamily_eigenspace_inf_eigenspace hB (hf.ne hij) x y

lemma jointEigenSpace_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : E →ₗ[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hc : Commute A B) :
    (⨆ c, JointEigenSpace A B c) = ⊤ := by
  classical
  apply top_unique
  rw [← hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB hc]
  apply iSup_le
  intro α
  apply iSup_le
  intro β
  by_cases hα : Module.End.HasEigenvalue A α
  · by_cases hβ : Module.End.HasEigenvalue B β
    · exact le_iSup_of_le (⟨β, hβ⟩, ⟨α, hα⟩) le_rfl
    · rw [Module.End.hasEigenvalue_iff.not_left.mp hβ, inf_bot_eq]
      exact bot_le
  · rw [Module.End.hasEigenvalue_iff.not_left.mp hα, bot_inf_eq]
    exact bot_le

lemma exists_joint_eigenbasis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : E →ₗ[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hc : Commute A B)
    {n : Type*} [Fintype n] (hn : Module.finrank ℂ E = Fintype.card n) :
    ∃ (b : OrthonormalBasis n ℂ E) (α β : n → ℝ),
      ∀ i, A (b i) = (α i : ℂ) • b i ∧ B (b i) = (β i : ℂ) • b i := by
  classical
  let V := JointEigenSpace A B
  have ho := jointEigenSpace_orthogonal hA hB
  have hi : DirectSum.IsInternal V := ho.isInternal_iff.mpr (by
    rw [jointEigenSpace_span hA hB hc]; exact Submodule.top_orthogonal_eq_bot)
  let b₀ := hi.subordinateOrthonormalBasis hn ho
  let c := fun i => hi.subordinateOrthonormalBasisIndex hn i ho
  have he (i : Fin (Fintype.card n)) :
      A (b₀ i) = ((c i).2 : ℂ) • b₀ i ∧ B (b₀ i) = ((c i).1 : ℂ) • b₀ i := by
    have hv := hi.subordinateOrthonormalBasis_subordinate hn i ho
    exact ⟨Module.End.mem_eigenspace_iff.mp hv.1, Module.End.mem_eigenspace_iff.mp hv.2⟩
  have hra (i : Fin (Fintype.card n)) : (((c i).2.val.re : ℝ) : ℂ) = ((c i).2 : ℂ) := by
    apply RCLike.conj_eq_iff_re.mp
    apply hA.conj_eigenvalue_eq_self
    exact (c i).2.property
  have hrb (i : Fin (Fintype.card n)) : (((c i).1.val.re : ℝ) : ℂ) = ((c i).1 : ℂ) := by
    apply RCLike.conj_eq_iff_re.mp
    apply hB.conj_eigenvalue_eq_self
    exact (c i).1.property
  refine ⟨b₀.reindex (Fintype.equivFin n).symm,
    fun i => (c (Fintype.equivFin n i)).2.val.re, fun i => (c (Fintype.equivFin n i)).1.val.re, ?_⟩
  intro i
  simpa only [OrthonormalBasis.reindex_apply, Equiv.symm_symm, hra, hrb] using he (Fintype.equivFin n i)

lemma exists_joint_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hc : Commute A B) :
    ∃ (U : unitary (Matrix n n ℂ)) (α β : n → ℝ),
      A = Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => (α i : ℂ)) ∧
      B = Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => (β i : ℂ)) := by
  have hAc : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hBc : B.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hcomm : Commute A.toEuclideanLin B.toEuclideanLin := by
    change (Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 B) =
      (Matrix.toLpLin 2 2 B).comp (Matrix.toLpLin 2 2 A)
    rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, hc.eq]
  obtain ⟨b, α, β, he⟩ := exists_joint_eigenbasis hAc hBc hcomm
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))
  let U : unitary (Matrix n n ℂ) :=
    ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hAU : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (α i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrArg (fun v : EuclideanSpace ℂ n => v i) (he j).1
    change (A *ᵥ ⇑(b j)) i = (α j : ℂ) * b j i at hh
    change (A *ᵥ ⇑(b j)) i = b j i * (α j : ℂ)
    simpa only [mul_comm] using hh
  have hBU : B * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (β i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrArg (fun v : EuclideanSpace ℂ n => v i) (he j).2
    change (B *ᵥ ⇑(b j)) i = (β j : ℂ) * b j i at hh
    change (B *ᵥ ⇑(b j)) i = b j i * (β j : ℂ)
    simpa only [mul_comm] using hh
  refine ⟨U, α, β, ?_, ?_⟩
  · rw [Unitary.conjStarAlgAut_apply, ← hAU, Matrix.mul_assoc, U.property.2, Matrix.mul_one]
  · rw [Unitary.conjStarAlgAut_apply, ← hBU, Matrix.mul_assoc, U.property.2, Matrix.mul_one]

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

lemma diagonal_intertwine_fn {n : Type*} [Fintype n] [DecidableEq n]
    (d e : n → ℝ) (W : Matrix n n ℂ)
    (h : Matrix.diagonal (fun i => (d i : ℂ)) * W = W * Matrix.diagonal (fun i => (e i : ℂ)))
    (f : ℝ → ℂ) :
    Matrix.diagonal (fun i => f (d i)) * W = W * Matrix.diagonal (fun i => f (e i)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hw : W i j = 0
  · simp [hw]
  · have hh := congrArg (fun A : Matrix n n ℂ => A i j) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
    rw [mul_comm (W i j)] at hh
    have heq : d i = e j := Complex.ofReal_injective ((mul_right_cancel₀ hw) hh)
    rw [heq, mul_comm]

lemma conj_diagonal_fn_congr {n : Type*} [Fintype n] [DecidableEq n]
    (U V : unitary (Matrix n n ℂ)) (d e : n → ℝ)
    (h : Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => (d i : ℂ)) =
      Unitary.conjStarAlgAut ℂ _ V (Matrix.diagonal fun i => (e i : ℂ))) (f : ℝ → ℂ) :
    Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => f (d i)) =
      Unitary.conjStarAlgAut ℂ _ V (Matrix.diagonal fun i => f (e i)) := by
  let W := star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)
  have hw : Matrix.diagonal (fun i => (d i : ℂ)) * W = W * Matrix.diagonal (fun i => (e i : ℂ)) := by
    have hh := congrArg (fun A : Matrix n n ℂ => star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) h
    dsimp only [W]
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, ← Matrix.mul_assoc (star (U : Matrix n n ℂ)) (U : Matrix n n ℂ), U.property.1, Matrix.one_mul, V.property.1, Matrix.mul_one] using hh
  have hh := diagonal_intertwine_fn d e W hw f
  have hh' := congrArg (fun A : Matrix n n ℂ => (U : Matrix n n ℂ) * A * star (V : Matrix n n ℂ)) hh
  simpa only [W, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : Matrix n n ℂ) (star (U : Matrix n n ℂ)),
    U.property.2, Matrix.one_mul, V.property.2, Matrix.mul_one] using hh'

lemma conj_diagonal_commute_fn {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (d : n → ℝ) (B : Matrix n n ℂ)
    (h : Commute (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => (d i : ℂ))) B)
    (f : ℝ → ℂ) :
    Commute (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal fun i => f (d i))) B := by
  let T := (Unitary.conjStarAlgAut ℂ _ U).symm B
  have ht : Matrix.diagonal (fun i => (d i : ℂ)) * T = T * Matrix.diagonal (fun i => (d i : ℂ)) := by
    have hh := h.map (Unitary.conjStarAlgAut ℂ _ U).symm
    simpa only [StarAlgEquiv.symm_apply_apply] using hh.eq
  have hf := diagonal_intertwine_fn d d T ht f
  have hh := congrArg (Unitary.conjStarAlgAut ℂ _ U) hf
  change _ * B = B * _
  simpa only [map_mul, T, StarAlgEquiv.apply_symm_apply] using hh

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
