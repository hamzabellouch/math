import OAI.Combinatorics.ThinTrees.FiniteSelection

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} {S : Type uS} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [CommRing R] [CommRing S]

omit [DecidableEq I] in
lemma basePencil_map (f : R →+* S) (M : Matrix D D R) (A : I → Matrix D D R) :
    (basePencil M A).map f=basePencil (M.map f) (fun i => (A i).map f) := by
  unfold basePencil
  rw [(MvPolynomial.map f).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  simp [Matrix.map_apply,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] [Fintype I] in
lemma eval_zero_map (f : R →+* S) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (p.map f)=f (MvPolynomial.eval (fun _ => 0) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp []
  | mul_X p k hp => simp

omit [DecidableEq I] in
lemma mixedEval_map (f : R →+* S) (dirs : List I) (M : Matrix D D R) (A : I → Matrix D D R) :
    f (mixedEval dirs M A)=mixedEval dirs (M.map f) (fun i => (A i).map f) := by
  unfold mixedEval
  rw [←eval_zero_map,←diffProduct_map,basePencil_map]

omit [DecidableEq I] in
lemma mixedChar_eval (A : I → Matrix D D R) (x : R) :
    (mixedChar A).eval x=mixedEval Finset.univ.toList (x • (1 : Matrix D D R)) A := by
  unfold mixedChar
  change Polynomial.evalRingHom x (mixedEval _ _ _) = _
  rw [mixedEval_map]
  congr 1
  · apply Matrix.ext
    intro a b
    by_cases h : a=b <;> simp [Matrix.map_apply,Matrix.smul_apply,h]
  · funext i
    apply Matrix.ext
    intro a b
    simp [Matrix.map_apply]

def translate (x : R) : MvPolynomial I R →+* MvPolynomial I R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i+MvPolynomial.C x)

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma translate_C (x r : R) : translate (I := I) x (MvPolynomial.C r)=MvPolynomial.C r := by
  simp [translate]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma translate_X (x : R) (i : I) : translate x (MvPolynomial.X i)=
    MvPolynomial.X i+MvPolynomial.C x := by
  simp [translate]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma translate_pderiv (x : R) (i : I) (p : MvPolynomial I R) :
    translate x (MvPolynomial.pderiv i p)=MvPolynomial.pderiv i (translate x p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [translate]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p k hp =>
    by_cases hk : k=i
    · subst k
      simp only [MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.pderiv_X_self,
        mul_one,hp]
      simp [translate]
    · simp only [MvPolynomial.pderiv_mul,map_mul,MvPolynomial.pderiv_X_of_ne hk,
        mul_zero,add_zero,hp]
      simp [translate,hk]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma translate_diffProduct (x : R) (dirs : List I) (p : MvPolynomial I R) :
    translate x (diffProduct dirs p)=diffProduct dirs (translate x p) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih => simp only [diffProduct_cons,ih,map_sub,translate_pderiv]

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
lemma eval_zero_translate (x : R) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (translate x p)=MvPolynomial.eval (fun _ => x) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [translate]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p k hp => simpa only [map_mul,translate_X,
      MvPolynomial.eval_add,MvPolynomial.eval_X,MvPolynomial.eval_C,zero_add] using congrArg (·*x) hp

omit [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
lemma translate_linear_sum (a : I → R) (x : R) :
    translate x (∑i, MvPolynomial.X i * MvPolynomial.C (a i))=
      (∑i, MvPolynomial.X i * MvPolynomial.C (a i))+MvPolynomial.C x*MvPolynomial.C (∑i, a i) := by
  simp only [map_sum,map_mul,translate_X,translate_C,add_mul,Finset.sum_add_distrib]
  rw [←Finset.mul_sum,←map_sum]

omit [DecidableEq I] in
lemma translate_pencil (A : I → Matrix D D R) (hsum : ∑i, A i=1) (x : R) :
    translate x (pencil A)=basePencil (x • (1 : Matrix D D R)) A := by
  let N : Matrix D D (MvPolynomial I R) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change translate x N.det = _
  rw [(translate x).map_det]
  unfold basePencil
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  change translate x (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  rw [translate_linear_sum]

  have hab := congrArg (fun M : Matrix D D R => M a b) hsum
  simp only [Matrix.sum_apply] at hab
  rw [hab]
  simp only [Matrix.add_apply,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
  exact add_comm _ _

lemma mixedChar_eval_diagonal (A : I → Matrix D D R) (hsum : ∑i, A i=1) (x : R) :
    (mixedChar A).eval x=MvPolynomial.eval (fun _ => x) (diffProduct Finset.univ.toList (pencil A)) := by
  rw [mixedChar_eval,mixedEval,←translate_pencil A hsum x,←translate_diffProduct,eval_zero_translate]

end StrongThinTree.MSS

end
end

end OAI
