import OAI.Combinatorics.ThinTrees.Translation

namespace OAI

universe uI uD uO

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {O : Type uO} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [Fintype O]

lemma mixedChar_roots_bound (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) {ε : ℝ} (hε : 0 < ε) (htr : ∀i, (A i).trace ≤ ε) :
    ∀r ∈ (mixedChar A).roots, r ≤ (1+Real.sqrt ε)^2 := by
  intro r hr
  by_contra! hlt
  have hp := skew_root_bound A hA hsum hε htr (fun _ => r-(1+Real.sqrt ε)^2)
    (fun _ => sub_nonneg.mpr hlt.le)
  have he : (fun _ : I => (1+Real.sqrt ε)^2)+(fun _ => r-(1+Real.sqrt ε)^2)=(fun _ => r) := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [he] at hp
  have hev := (Polynomial.mem_roots (by intro h; simp [h] at hr)).mp hr
  have hd : realDifferentialProduct Finset.univ.toList (pencil A)=diffProduct Finset.univ.toList (pencil A) :=
    (diffProduct_foldl _ _).symm
  rw [hd,←mixedChar_eval_diagonal A hsum r,hev] at hp
  exact lt_irrefl _ hp

lemma matrix_le_of_roots {A : Matrix D D ℝ} (hA : A.IsHermitian) {b : ℝ}
    (hr : ∀r ∈ A.charpoly.roots, r ≤ b) : A ≤ b • (1 : Matrix D D ℝ) := by
  have hh : A ≤ algebraMap ℝ (Matrix D D ℝ) b := by
    apply le_algebraMap_of_spectrum_le (ha := Matrix.isHermitian_iff_isSelfAdjoint.mp hA)
    intro r hr'
    exact hr r ((Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mpr
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hr'))
  simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem small_vectors (w : I → O → ℝ) (v : I → O → D → ℝ)
    (hw : ∀i o, 0 < w i o) (hprob : ∀i, ∑o, w i o=1)
    (hiso : ∑i, ∑o, w i o • Matrix.vecMulVec (v i o) (v i o)=1)
    {ε : ℝ} (hε : 0 < ε)
    (hsize : ∀i, (∑o, w i o • Matrix.vecMulVec (v i o) (v i o)).trace ≤ ε) :
    ∃f : I → O, (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))) ≤
      (1+Real.sqrt ε)^2 • (1 : Matrix D D ℝ) := by
  have hA : ∀i, (∑o, w i o • Matrix.vecMulVec (v i o) (v i o)).PosSemidef :=
    fun i => Matrix.posSemidef_sum _ (fun o _ => (rankOne_posSemidef _).smul (hw i o).le)
  obtain ⟨f,hf⟩ := finite_selection w v hw hprob (mixedChar_roots_bound _ hA hiso hε hsize)
  exact ⟨f,matrix_le_of_roots (Matrix.posSemidef_sum _ (fun i _ => rankOne_posSemidef _)).isHermitian hf⟩

end StrongThinTree.MSS

end
end

end OAI
