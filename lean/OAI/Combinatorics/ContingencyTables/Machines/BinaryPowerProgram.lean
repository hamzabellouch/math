import OAI.Combinatorics.ContingencyTables.Machines.IntegerMatrixProgram

namespace OAI

/-! # Binary powers with a polynomial bound in the exponent and input bits -/

namespace ContingencyTables.BinaryPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def setup (z : ℕ×ℕ) : ℕ×(List (List ℕ)×List ℕ) := (z.2,([[z.1]],[1]))

def singleton {A : Type} [Codec A] : Realizer (fun a : A => [a]) :=
  composition (pair identity (constant [])) listCons

lemma polynomial_singleton {A : Type} [Codec A] : PolynomialTime (singleton (A := A)) :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
    polynomial_listCons

def setupRealizer : Realizer setup :=
  pair second (pair (composition (composition first singleton) singleton) (constant [1]))

lemma polynomial_setup : PolynomialTime setupRealizer :=
  polynomial_pair polynomial_second (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_singleton)
      polynomial_singleton) (polynomial_constant [1]))

def power (z : ℕ×ℕ) : ℕ := (IntegerMatrixPrograms.iterate (setup z)).headD 0

def powerRealizer : Realizer power :=
  composition (composition setupRealizer IntegerMatrixPrograms.iterateRealizer) (head 0)

theorem power_eq (a N : ℕ) : power (a,N)=a^N := by
  have hnum (n : ℕ) :
      IntegerPropagation.numerators (fun _ _ : Fin 1 => a) 0 n 0=a^n := by
    induction n with
    | zero => simp [IntegerPropagation.numerators]
    | succ n ih => simp [IntegerPropagation.numerators,ih,pow_succ]
  have hi:=IntegerMatrixPrograms.iterate_ofFn (fun _ _ : Fin 1 => a) 0 N
  have hs : (List.ofFn fun _ : Fin 1 => List.ofFn fun _ : Fin 1 => a)=[[a]] := by simp
  have hv : (List.ofFn fun x : Fin 1 => if x=0 then (1:ℕ) else 0)=[1] := by simp
  rw [hs,hv] at hi
  unfold power setup
  rw [hi]
  simpa using hnum N

/-- Multiplication uses binary operands; only the exponent controls the
number of iterations. This is sufficient for the dyadic tabulation. -/
theorem work_power : WorkBound powerRealizer (fun z => z.2+weight z.1) := by
  unfold powerRealizer
  apply work_then_polynomial _ (polynomial_head 0)
  apply work_composition
    (work_of_polynomial polynomial_setup (5*Polynomial.X+3) (by
      intro z
      have hn:=weight_nat_numeric z.2
      rw [←Prod.eta z,weight_prod]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X]
      omega)) IntegerMatrixPrograms.work_iterate (Polynomial.X+12)
  intro z
  simp only [setup,weight_prod,weight_cons,weight_nil,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  have hw:=weight_nat_le (1:ℕ)
  norm_num at hw
  omega

end ContingencyTables.BinaryPowerPrograms

end OAI
