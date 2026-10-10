import OAI.Combinatorics.ThinTrees.RealRoots

namespace OAI

universe uI uD uO

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {O : Type uO} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [Fintype O]

omit [DecidableEq D] in
lemma rankOne_posSemidef (v : D → ℝ) : (Matrix.vecMulVec v v).PosSemidef := by
  simpa using Matrix.posSemidef_vecMulVec_self_star v

lemma mixedChar_segment (j : I) (A : I → Matrix D D ℝ) (B : Matrix D D ℝ) (t : ℝ) :
    (1-t) • mixedChar A+t • mixedChar (Function.update A j B)=
      mixedChar (Function.update A j ((1-t) • A j+t • B)) := by
  have hh := mixedChar_mean (O := Bool) j A (fun b => if b then t else 1-t)
    (fun b => if b then B else A j) (by simp)
  have hm : (∑b : Bool, (if b then t else 1-t) • (if b then B else A j))=
      (1-t) • A j+t • B := by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true,↓reduceIte]
    exact add_comm _ _
  rw [hm,Fintype.sum_bool] at hh
  simp only [Bool.false_eq_true,↓reduceIte] at hh
  rw [Function.update_eq_self] at hh
  rw [hh]
  exact add_comm _ _

omit [Fintype I] in
omit [DecidableEq D] in
lemma partial_posSemidef (s : Finset I) (A : I → Matrix D D ℝ)
    (w : I → O → ℝ) (v : I → O → D → ℝ) (hw : ∀i o, 0 ≤ w i o)
    (hA : ∀i ∈ s, A i=∑o, w i o • Matrix.vecMulVec (v i o) (v i o))
    (hfixed : ∀i, i ∉ s → ∃o, A i=Matrix.vecMulVec (v i o) (v i o)) :
    ∀i, (A i).PosSemidef := by
  intro i
  by_cases hi : i ∈ s
  · rw [hA i hi]
    exact Matrix.posSemidef_sum _ (fun o _ => (rankOne_posSemidef _).smul (hw i o))
  · obtain ⟨o,ho⟩ := hfixed i hi
    rw [ho]
    exact rankOne_posSemidef _

lemma finite_selection_partial (s : Finset I) (A : I → Matrix D D ℝ)
    (w : I → O → ℝ) (v : I → O → D → ℝ) (hw : ∀i o, 0 < w i o)
    (hsum : ∀i, ∑o, w i o=1)
    (hA : ∀i ∈ s, A i=∑o, w i o • Matrix.vecMulVec (v i o) (v i o))
    (hfixed : ∀i, i ∉ s → ∃o, A i=Matrix.vecMulVec (v i o) (v i o))
    {b : ℝ} (hroot : ∀r ∈ (mixedChar A).roots, r ≤ b) :
    ∃f : I → O, ∀r ∈ (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))).charpoly.roots, r ≤ b := by
  induction s using Finset.induction_on generalizing A with
  | empty =>
    have hh : ∀i, ∃o, A i=Matrix.vecMulVec (v i o) (v i o) := fun i => hfixed i (by simp)
    choose f hf using hh
    refine ⟨f,?_⟩
    have hrank : ∀i, ∃a c, A i=Matrix.vecMulVec a c := fun i => ⟨_,_,hf i⟩
    rw [mixedChar_rankOne A hrank] at hroot
    simpa only [hf] using hroot
  | @insert j s hj ih =>
    let B : O → Matrix D D ℝ := fun o => Matrix.vecMulVec (v j o) (v j o)
    let child : O → I → Matrix D D ℝ := fun o => Function.update A j (B o)
    have hchildA : ∀o i, i ∈ s → child o i=∑a, w i a • Matrix.vecMulVec (v i a) (v i a) := by
      intro o i hi
      dsimp only [child]
      rw [Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi))]
      exact hA i (Finset.mem_insert_of_mem hi)
    have hchildfixed : ∀o i, i ∉ s → ∃a, child o i=Matrix.vecMulVec (v i a) (v i a) := by
      intro o i hi
      by_cases hij : i=j
      · subst i; exact ⟨o,by simp [child,B]⟩
      · dsimp only [child]
        rw [Function.update_of_ne hij]
        exact hfixed i (by simp [hij,hi])
    have hmon : ∀o, (mixedChar (child o)).IsMonicOfDegree (Fintype.card D) := by
      intro o
      apply mixedChar_monic_partial s _ w v v hsum (hchildA o)
      intro i hi
      obtain ⟨a,ha⟩ := hchildfixed o i hi
      exact ⟨_,_,ha⟩
    have hmean : (∑o, w j o • mixedChar (child o))=mixedChar A := by
      rw [←mixedChar_mean j A (w j) B (hsum j),←hA j (by simp)]
      simp
    have hpsd := partial_posSemidef (insert j s) A w v (fun i o => (hw i o).le) hA hfixed
    have hsplit : ∀o t, t ∈ Set.Icc (0 : ℝ) 1 →
        ((1-t) • (∑a, w j a • mixedChar (child a))+t • mixedChar (child o)).Splits := by
      intro o t ht
      rw [hmean,mixedChar_segment]
      apply mixedChar_splits
      intro i
      by_cases hij : i=j
      · subst i
        simp only [Function.update_self]
        exact ((hpsd j).smul (sub_nonneg.mpr ht.2)).add ((rankOne_posSemidef _).smul ht.1)
      · rw [Function.update_of_ne hij]
        exact hpsd i
    obtain ⟨o,ho⟩ := Selection.selection (fun o => mixedChar (child o)) hmon (w j) (hw j) (hsum j)
      hsplit (by simpa only [hmean] using hroot)
    exact ih (child o) (hchildA o) (hchildfixed o) ho

lemma finite_selection (w : I → O → ℝ) (v : I → O → D → ℝ)
    (hw : ∀i o, 0 < w i o) (hsum : ∀i, ∑o, w i o=1)
    {b : ℝ} (hroot : ∀r ∈ (mixedChar (fun i => ∑o, w i o • Matrix.vecMulVec (v i o) (v i o))).roots, r ≤ b) :
    ∃f : I → O, ∀r ∈ (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))).charpoly.roots, r ≤ b :=
  finite_selection_partial Finset.univ _ w v hw hsum (by intros; rfl) (by simp) hroot

end StrongThinTree.MSS

end
end

end OAI
