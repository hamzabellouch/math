import OAI.Combinatorics.ThinTrees.MixedPolynomial

namespace OAI

universe uI uD uR uO uO2 uO3

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

lemma zeroDiff_update (j : I) (M B : Matrix D D R) (A : I → Matrix D D R) :
    zeroDiff j (basePencil M (Function.update A j B))=
      (M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)).det-
      detLinear (M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)) (B.map (MvPolynomial.C : R →+* MvPolynomial I R)) := by
  rw [zeroDiff_basePencil,Function.update_self]
  have hh : ∑i ∈ Finset.univ.erase j, (MvPolynomial.X i : MvPolynomial I R) •
      ((Function.update A j B) i).map (MvPolynomial.C : R →+* MvPolynomial I R)=
      ∑i ∈ Finset.univ.erase j, (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hh]

omit [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] in
lemma matrix_map_mean {O : Type uO} [Fintype O] (w : O → R) (B : O → Matrix D D R) :
    (∑o, w o • B o).map (MvPolynomial.C : R →+* MvPolynomial I R)=
      ∑o, (MvPolynomial.C (w o) : MvPolynomial I R) • (B o).map (MvPolynomial.C : R →+* MvPolynomial I R) := by
  apply Matrix.ext
  intro a b
  simp [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply]

lemma zeroDiff_affine {O : Type uO2} [Fintype O] (j : I) (M : Matrix D D R)
    (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R) (hw : ∑o, w o=1) :
    zeroDiff j (basePencil M (Function.update A j (∑o, w o • B o)))=
      ∑o, w o • zeroDiff j (basePencil M (Function.update A j (B o))) := by
  simp only [zeroDiff_update]
  let N := M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i ∈ Finset.univ.erase j,
    (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)
  change N.det-detLinear N ((∑o, w o • B o).map (MvPolynomial.C : R →+* MvPolynomial I R))=
    ∑o, w o • (N.det-detLinear N ((B o).map (MvPolynomial.C : R →+* MvPolynomial I R)))
  rw [matrix_map_mean,map_sum]
  simp only [map_smul,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hw,one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro o _
  exact MvPolynomial.C_mul'

lemma mixedEval_affine_cons {O : Type uO3} [Fintype O] (j : I) (dirs : List I) (hj : j ∉ dirs)
    (M : Matrix D D R) (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R)
    (hw : ∑o, w o=1) :
    mixedEval (j::dirs) M (Function.update A j (∑o, w o • B o))=
      ∑o, w o * mixedEval (j::dirs) M (Function.update A j (B o)) := by
  simp only [mixedEval,eval_zero_diffProduct_cons j dirs hj]
  rw [zeroDiff_affine j M A w B hw,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [map_smul]
  simp only [←MvPolynomial.C_mul',map_mul,MvPolynomial.eval_C]

end StrongThinTree.MSS

end
end

end OAI
