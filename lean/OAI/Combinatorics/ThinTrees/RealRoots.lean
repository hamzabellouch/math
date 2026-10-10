import OAI.Combinatorics.ThinTrees.Monicity

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder ComplexOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def fullPencil (A : I → Matrix D D R) : MvPolynomial (Option I) R :=
  pencil (fun o => o.elim 1 A)

omit [DecidableEq I] in
lemma coefficientX_fullPencil (A : I → Matrix D D R) :
    coefficientX (fullPencil A)=basePencil ((Polynomial.X : R[X]) • (1 : Matrix D D R[X]))
      (fun i => (A i).map Polynomial.C) := by
  let N : Matrix D D (MvPolynomial (Option I) R) := fun a b =>
    ∑i : Option I, MvPolynomial.X i * MvPolynomial.C ((i.elim (1 : Matrix D D R) A) a b)
  change coefficientX N.det = _
  unfold basePencil
  rw [(coefficientX (I := I) (R := R)).map_det N]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  change coefficientX (∑i : Option I, MvPolynomial.X i * MvPolynomial.C ((i.elim 1 A) a b))=_
  simp only [Fintype.sum_option,Option.elim]
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
  by_cases h : a=b <;> simp [Matrix.one_apply,h]

lemma mixedChar_uniSlice (A : I → Matrix D D R) : mixedChar A=
    uniSlice (diffProduct ((Finset.univ.toList : List I).map some) (fullPencil A)) := by
  rw [←eval_zero_coefficientX,coefficientX_diffProduct,coefficientX_fullPencil]
  rfl

omit [DecidableEq I] in
lemma fullPencil_map {S : Type uS} [CommRing S] (f : R →+* S) (A : I → Matrix D D R) :
    (fullPencil A).map f=fullPencil (fun i => (A i).map f) := by
  unfold fullPencil
  rw [pencil_map]
  congr 1
  funext i
  cases i with
  | none => simp
  | some i => rfl

omit [DecidableEq I] in
lemma fullPencil_stable (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef) :
    RealStable (fullPencil A) := by
  unfold RealStable
  rw [fullPencil_map]
  apply determinantPencil_stable
  · intro i
    cases i with
    | none => exact Matrix.PosSemidef.one
    | some i => exact posSemidef_complex (hA i)
  · rw [Fintype.sum_option]
    simpa only [Option.elim] using (Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum Finset.univ (fun i _ => posSemidef_complex (hA i))))

lemma mixedChar_splits (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef) :
    (mixedChar A).Splits := by
  by_cases h0 : mixedChar A=0
  · rw [h0]; simp
  apply splits_of_upper_half_plane
  rw [mixedChar_uniSlice,←uniSlice_map,←diffProduct_map]
  have hs : Stable (diffProduct ((Finset.univ.toList : List I).map some)
      ((fullPencil A).map (algebraMap ℝ ℂ))) := by
    rw [diffProduct_foldl]
    exact (fullPencil_stable A hA).differentialProduct _
  rw [uniSlice_eq_slice]
  apply hs.slice_boundary _ (by simp) none
  rw [←uniSlice_eq_slice,diffProduct_map,uniSlice_map,←mixedChar_uniSlice]
  exact Polynomial.map_ne_zero h0

end StrongThinTree.MSS

end
end

end OAI
