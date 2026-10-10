import OAI.Combinatorics.ThinTrees.Characteristic

namespace OAI

universe uI uD uO

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {O : Type uO} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [Fintype O]

lemma mixedChar_mean (j : I) (A : I → Matrix D D ℝ) (w : O → ℝ)
    (B : O → Matrix D D ℝ) (hw : ∑o, w o=1) :
    mixedChar (Function.update A j (∑o, w o • B o))=
      ∑o, w o • mixedChar (Function.update A j (B o)) := by
  simpa only [Polynomial.smul_eq_C_mul] using mixedChar_affine j A w B hw

lemma mixedChar_monic_partial (s : Finset I) (A : I → Matrix D D ℝ)
    (w : I → O → ℝ) (u v : I → O → D → ℝ) (hw : ∀i, ∑o, w i o=1)
    (hA : ∀i ∈ s, A i=∑o, w i o • Matrix.vecMulVec (u i o) (v i o))
    (hfixed : ∀i, i ∉ s → ∃a b, A i=Matrix.vecMulVec a b) :
    (mixedChar A).IsMonicOfDegree (Fintype.card D) := by
  induction s using Finset.induction_on generalizing A with
  | empty =>
    rw [mixedChar_rankOne A (fun i => hfixed i (by simp))]
    exact ⟨Matrix.charpoly_natDegree_eq_dim _,Matrix.charpoly_monic _⟩
  | @insert j s hj ih =>
    let B : O → Matrix D D ℝ := fun o => Matrix.vecMulVec (u j o) (v j o)
    have hAj : A j=∑o, w j o • B o := hA j (by simp)
    have he : mixedChar A=∑o, w j o • mixedChar (Function.update A j (B o)) := by
      rw [←mixedChar_mean j A (w j) B (hw j)]
      congr 1
      rw [←hAj]
      simp
    rw [he]
    apply Selection.monic_mean _ _ (w j) (hw j)
    intro o
    apply ih
    · intro i hi
      rw [Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi))]
      exact hA i (Finset.mem_insert_of_mem hi)
    · intro i hi
      by_cases hij : i=j
      · subst i
        exact ⟨u j o,v j o,by simp [B]⟩
      · rw [Function.update_of_ne hij]
        exact hfixed i (by simp [hij,hi])

end StrongThinTree.MSS

end
end

end OAI
