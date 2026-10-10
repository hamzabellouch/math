import OAI.Combinatorics.ThinTrees.Interlacing

namespace OAI

universe uI uD uR uO uO2

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

lemma univ_perm_cons (j : I) : (Finset.univ.toList : List I).Perm (j::(Finset.univ.erase j).toList) := by
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_cons.mpr
    ⟨by simp, Finset.nodup_toList _⟩)).mpr
  intro i
  simp
  tauto

lemma mixedEval_affine {O : Type uO} [Fintype O] (j : I) (M : Matrix D D R)
    (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R) (hw : ∑o, w o=1) :
    mixedEval Finset.univ.toList M (Function.update A j (∑o, w o • B o))=
      ∑o, w o * mixedEval Finset.univ.toList M (Function.update A j (B o)) := by
  have hh : ∀A : I → Matrix D D R, mixedEval Finset.univ.toList M A=
      mixedEval (j::(Finset.univ.erase j).toList) M A := by
    intro A
    unfold mixedEval
    rw [diffProduct_perm (univ_perm_cons j)]
  simp only [hh]
  exact mixedEval_affine_cons j _ (by simp) M A w B hw

def mixedChar (A : I → Matrix D D R) : R[X] :=
  mixedEval Finset.univ.toList ((Polynomial.X : R[X]) • (1 : Matrix D D R[X]))
    (fun i => (A i).map Polynomial.C)

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma map_update (A : I → Matrix D D R) (j : I) (B : Matrix D D R) :
    (fun i => ((Function.update A j B) i).map Polynomial.C)=
      Function.update (fun i => (A i).map Polynomial.C) j (B.map Polynomial.C) := by
  funext i
  by_cases hi : i=j <;> simp [hi]

lemma mixedChar_affine {O : Type uO2} [Fintype O] (j : I)
    (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R) (hw : ∑o, w o=1) :
    mixedChar (Function.update A j (∑o, w o • B o))=
      ∑o, Polynomial.C (w o) * mixedChar (Function.update A j (B o)) := by
  have hm : (∑o, w o • B o).map Polynomial.C=
      ∑o, Polynomial.C (w o) • (B o).map Polynomial.C := by
    apply Matrix.ext
    intro a b
    simp [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply]
  simp only [mixedChar,map_update,hm]
  exact mixedEval_affine j _ _ (fun o => Polynomial.C (w o)) _ (by simpa using congrArg Polynomial.C hw)

lemma mixedChar_rankOne (A : I → Matrix D D R) (hA : ∀i, ∃u v, A i=Matrix.vecMulVec u v) :
    mixedChar A=(∑i, A i).charpoly := by
  unfold mixedChar
  rw [mixedEval_rankOne _ (Finset.nodup_toList _)]
  · rw [Finset.sum_map_toList]
    have he : (∑i, (A i).map Polynomial.C)=(∑i, A i).map Polynomial.C := by
      apply Matrix.ext
      intro a b
      simp [Matrix.sum_apply,Matrix.map_apply]
    rw [he]
    unfold Matrix.charpoly
    apply congrArg Matrix.det
    apply Matrix.ext
    intro a b
    by_cases hab : a=b <;> simp [Matrix.sub_apply,Matrix.smul_apply,Matrix.map_apply,hab]
  · intro i _
    obtain ⟨u,v,h⟩ := hA i
    refine ⟨fun a => Polynomial.C (u a),fun a => Polynomial.C (v a),?_⟩
    rw [h]
    apply Matrix.ext
    intro a b
    simp [Matrix.vecMulVec,Matrix.map_apply]

end StrongThinTree.MSS

end
end

end OAI
