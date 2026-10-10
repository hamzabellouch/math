import OAI.Combinatorics.ThinTrees.RootBound

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} {S : Type uS} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [CommRing R] [CommRing S]

def coefficientX : MvPolynomial (Option I) R →+* MvPolynomial I R[X] :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (fun o => o.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X)

def uniSlice : MvPolynomial (Option I) R →+* R[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun o => o.elim Polynomial.X (fun _ => 0))

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma coefficientX_C (r : R) : coefficientX (I := I) (MvPolynomial.C r)=
    MvPolynomial.C (Polynomial.C r) := by simp [coefficientX]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma coefficientX_X (i : Option I) : coefficientX (R := R) (MvPolynomial.X i)=
    i.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X := by simp [coefficientX]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma uniSlice_C (r : R) : uniSlice (I := I) (MvPolynomial.C r)=Polynomial.C r := by
  simp [uniSlice]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
@[simp] lemma uniSlice_X (i : Option I) : uniSlice (R := R) (MvPolynomial.X i)=
    i.elim Polynomial.X (fun _ => 0) := by simp [uniSlice]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma coefficientX_pderiv (i : I) (p : MvPolynomial (Option I) R) :
    coefficientX (MvPolynomial.pderiv (some i) p)=MvPolynomial.pderiv i (coefficientX p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    rw [MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,map_mul,MvPolynomial.pderiv_mul,hp]
    cases k with
    | none => simp
    | some k => by_cases hk : k=i <;> simp [hk]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma coefficientX_diffProduct (dirs : List I) (p : MvPolynomial (Option I) R) :
    coefficientX (diffProduct (dirs.map some) p)=diffProduct dirs (coefficientX p) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih =>
    simp only [List.map_cons,diffProduct_cons,ih,map_sub,coefficientX_pderiv]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
lemma eval_zero_coefficientX (p : MvPolynomial (Option I) R) :
    MvPolynomial.eval (fun _ => 0) (coefficientX p)=uniSlice p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p k hp =>
    cases k <;> simp only [map_mul,coefficientX_X,uniSlice_X,Option.elim,
      MvPolynomial.eval_C,MvPolynomial.eval_X,mul_zero,hp]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
lemma uniSlice_map (f : R →+* S) (p : MvPolynomial (Option I) R) :
    uniSlice (p.map f)=(uniSlice p).map f := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp => cases k <;> simp [hp]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
lemma diffProduct_map (f : R →+* S) (dirs : List I) (p : MvPolynomial I R) :
    diffProduct dirs (p.map f)=(diffProduct dirs p).map f := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih =>
    simp only [diffProduct_cons,MvPolynomial.pderiv_map,←map_sub,ih]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma uniSlice_eq_slice (p : MvPolynomial (Option I) ℂ) :
    uniSlice p=slice p (fun _ => 0) none := by
  change MvPolynomial.eval₂ Polynomial.C (fun o : Option I => o.elim X (fun _ => 0)) p = _
  unfold slice
  apply congrArg (fun z => MvPolynomial.eval₂ Polynomial.C z p)
  funext i
  cases i <;> simp

end StrongThinTree.MSS

end
end

end OAI
