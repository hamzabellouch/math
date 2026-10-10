import OAI.Combinatorics.ThinTrees.Barrier

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def basePencil (M : Matrix D D R) (A : I → Matrix D D R) : MvPolynomial I R :=
  (M.map MvPolynomial.C + ∑i, (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).det

def zeroSub (j : I) : MvPolynomial I R →+* MvPolynomial I R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Function.update MvPolynomial.X j 0)

def zeroDiff (j : I) (p : MvPolynomial I R) : MvPolynomial I R :=
  zeroSub j (p-MvPolynomial.pderiv j p)

def view (j : I) : MvPolynomial I R →+* (MvPolynomial I R)[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (Function.update (fun i => Polynomial.C (MvPolynomial.X i)) j Polynomial.X)

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma view_C (j : I) (r : R) : view j (MvPolynomial.C r)=C (MvPolynomial.C r) := by
  simp [view]

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma view_X (j i : I) : view (R := R) j (MvPolynomial.X i)=
    if i=j then X else C (MvPolynomial.X i) := by
  simp [view,Function.update_apply]

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma zeroSub_C (j : I) (r : R) : zeroSub j (MvPolynomial.C r)=MvPolynomial.C r := by
  simp [zeroSub]

omit [Fintype I] [Fintype D] [DecidableEq D] in
@[simp] lemma zeroSub_X (j i : I) : zeroSub (R := R) j (MvPolynomial.X i)=
    if i=j then 0 else MvPolynomial.X i := by
  simp [zeroSub,Function.update_apply]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma view_derivative (j : I) (p : MvPolynomial I R) :
    (view j p).derivative=view j (MvPolynomial.pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.derivative_mul,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hp]
    by_cases hi : i=j
    · subst i; simp
    · simp [hi]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma view_zero (j : I) (p : MvPolynomial I R) :
    (view j p).eval 0=zeroSub j p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    by_cases hi : i=j
    · subst i; simp
    · simp [hi,hp]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma zeroDiff_coeff (j : I) (p : MvPolynomial I R) :
    zeroDiff j p=(view j p).coeff 0-(view j p).coeff 1 := by
  rw [zeroDiff,map_sub,←view_zero,←view_zero,←view_derivative]
  simp [←coeff_zero_eq_eval_zero,coeff_derivative]

omit [Fintype D] [DecidableEq D] in
lemma view_affine_entry (j : I) (c : R) (a : I → R) :
    view j (MvPolynomial.C c+∑i, MvPolynomial.X i*MvPolynomial.C (a i))=
    C (MvPolynomial.C c+∑i ∈ Finset.univ.erase j, MvPolynomial.X i*MvPolynomial.C (a i))+
      X*C (MvPolynomial.C (a j)) := by
  simp only [map_add,map_sum,map_mul,view_C,view_X]
  rw [←Finset.add_sum_erase Finset.univ
    (fun i => (if i=j then X else C (MvPolynomial.X i))*C (MvPolynomial.C (a i))) (Finset.mem_univ j)]
  simp only [ite_true]
  have hh : ∑i ∈ Finset.univ.erase j,
      (if i=j then X else C (MvPolynomial.X i))*C (MvPolynomial.C (a i))=
      ∑i ∈ Finset.univ.erase j, C (MvPolynomial.X i)*C (MvPolynomial.C (a i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_erase.mp hi).1]
  rw [hh]
  abel

omit [Fintype D] [DecidableEq D] in
lemma view_baseMatrix (j : I) (M : Matrix D D R) (A : I → Matrix D D R) :
    (M.map MvPolynomial.C + ∑i, (MvPolynomial.X i : MvPolynomial I R) •
      (A i).map MvPolynomial.C).map (view j)=
      (M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).map Polynomial.C +
        (X : (MvPolynomial I R)[X]) • ((A j).map MvPolynomial.C).map Polynomial.C := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.map_apply,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact view_affine_entry j (M a b) (fun i => A i a b)

lemma view_basePencil (j : I) (M : Matrix D D R) (A : I → Matrix D D R) :
    view j (basePencil M A)=
      ((M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).map Polynomial.C +
        (X : (MvPolynomial I R)[X]) • ((A j).map MvPolynomial.C).map Polynomial.C).det := by
  unfold basePencil
  rw [(view j).map_det]
  exact congrArg Matrix.det (view_baseMatrix j M A)

lemma zeroDiff_basePencil (j : I) (M : Matrix D D R) (A : I → Matrix D D R) :
    zeroDiff j (basePencil M A)=
      (M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).det-
      detLinear (M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C) ((A j).map MvPolynomial.C) := by
  rw [zeroDiff_coeff,view_basePencil,det_linear_pencil_coeff_one]
  congr 1
  rw [coeff_zero_eq_eval_zero,show Polynomial.eval (0 : MvPolynomial I R)=Polynomial.evalRingHom 0 from rfl,
    (Polynomial.evalRingHom (0 : MvPolynomial I R)).map_det]
  congr 1
  apply Matrix.ext
  intro a b
  simp

end StrongThinTree.MSS

end
end

end OAI
