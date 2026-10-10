import OAI.Combinatorics.ThinTrees.Affine

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

lemma det_sub_rankOne (M : Matrix D D R) (u v : D → R) :
    (M-Matrix.vecMulVec u v).det=M.det-detLinear M (Matrix.vecMulVec u v) := by
  simpa only [Matrix.neg_vecMulVec,sub_eq_add_neg,map_neg] using det_add_rankOne M (-u) v

omit [Fintype D] [DecidableEq D] in
lemma sum_pencil_update_zero (A : I → Matrix D D R) (j : I) :
    ∑i, (MvPolynomial.X i : MvPolynomial I R) • ((Function.update A j 0) i).map (MvPolynomial.C : R →+* MvPolynomial I R)=
    ∑i ∈ Finset.univ.erase j, (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R) := by
  rw [←Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self,Matrix.map_zero,map_zero,smul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

lemma zeroDiff_rankOne (M : Matrix D D R) (A : I → Matrix D D R) (j : I)
    (u v : D → R) (h : A j=Matrix.vecMulVec u v) :
    zeroDiff j (basePencil M A)=basePencil (M-A j) (Function.update A j 0) := by
  rw [zeroDiff_basePencil,basePencil,sum_pencil_update_zero]
  have hm : (A j).map (MvPolynomial.C : R →+* MvPolynomial I R)=
      Matrix.vecMulVec (fun a => MvPolynomial.C (u a)) (fun a => MvPolynomial.C (v a)) := by
    rw [h]
    apply Matrix.ext
    intro a b
    simp [Matrix.vecMulVec,Matrix.map_apply]
  rw [hm,←det_sub_rankOne]
  apply congrArg Matrix.det
  rw [←hm]
  apply Matrix.ext
  intro a b
  simp only [Matrix.sub_apply,Matrix.map_apply,Matrix.add_apply,map_sub]
  abel

omit [DecidableEq I] in
lemma basePencil_eval (M : Matrix D D R) (A : I → Matrix D D R) (z : I → R) :
    MvPolynomial.eval z (basePencil M A)=(M+∑i, z i • A i).det := by
  unfold basePencil
  rw [(MvPolynomial.eval z).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  change MvPolynomial.eval z ((M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i,
    (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)) a b)=_
  simp [Matrix.map_apply,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] in
lemma mixedEval_nil (M : Matrix D D R) (A : I → Matrix D D R) : mixedEval [] M A=M.det := by
  rw [mixedEval,diffProduct_nil,basePencil_eval]
  simp

lemma mixedEval_rankOne (dirs : List I) (hd : dirs.Nodup) (M : Matrix D D R)
    (A : I → Matrix D D R) (hA : ∀i ∈ dirs, ∃u v, A i=Matrix.vecMulVec u v) :
    mixedEval dirs M A=(M-(dirs.map A).sum).det := by
  induction dirs generalizing M A with
  | nil => simp [mixedEval_nil]
  | cons j dirs ih =>
    have hj : j ∉ dirs := (List.nodup_cons.mp hd).1
    obtain ⟨u,v,hjv⟩ := hA j (List.mem_cons_self)
    have he : mixedEval (j::dirs) M A=mixedEval dirs (M-A j) (Function.update A j 0) := by
      rw [mixedEval,eval_zero_diffProduct_cons j dirs hj,zeroDiff_rankOne M A j u v hjv]
      rfl
    rw [he,ih (List.nodup_cons.mp hd).2]
    · have hu : dirs.map (Function.update A j 0)=dirs.map A := by
        apply List.map_congr_left
        intro i hi
        exact Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi)) _ _
      rw [hu,List.map_cons,List.sum_cons]
      apply congrArg Matrix.det
      abel
    · intro i hi
      rw [Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi))]
      exact hA i (List.mem_cons_of_mem _ hi)

end StrongThinTree.MSS

end
end

end OAI
