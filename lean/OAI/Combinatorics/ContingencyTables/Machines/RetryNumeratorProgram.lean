import OAI.Combinatorics.ContingencyTables.Machines.BinaryPowerProgram
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLaw

namespace OAI

/-! # Binary first-success numerators via a two-coordinate recurrence -/

namespace ContingencyTables.RetryNumeratorPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

/-- Unary trial count; denominator, failure count, success count, fallback match. -/
abbrev Input := List Bool×((ℕ×ℕ)×(ℕ×Bool))

def twoEntries {A : Type} [Codec A] : Realizer (fun x : A×A => [x.1,x.2]) :=
  composition (pair first (composition second BinaryPowerPrograms.singleton)) listCons

lemma polynomial_twoEntries {A : Type} [Codec A] : PolynomialTime (twoEntries (A := A)) :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second BinaryPowerPrograms.polynomial_singleton))
    polynomial_listCons

def setup (z : Input) : ℕ×(List (List ℕ)×List ℕ) :=
  (z.1.length,([[z.2.1.2,z.2.2.1],[0,z.2.1.1]],[(if z.2.2.2 then 1 else 0),1]))

def setupRealizer : Realizer setup := by
  let Q : Realizer (fun z : Input => z.2.1.1) := composition (composition second first) first
  let phi : Realizer (fun z : Input => z.2.1.2) := composition (composition second first) second
  let alpha : Realizer (fun z : Input => z.2.2.1) := composition (composition second second) first
  let hit : Realizer (fun z : Input => z.2.2.2) := composition (composition second second) second
  let column1 := composition (pair phi alpha) twoEntries
  let column2 := composition (pair (constant 0) Q) twoEntries
  let matrix := composition (pair column1 column2) twoEntries
  let initial := choose hit (constant 1) (constant 0)
  let vector := composition (pair initial (constant 1)) twoEntries
  exact pair (composition first listLength) (pair matrix vector)

lemma polynomial_setup : PolynomialTime setupRealizer := by
  have hQ : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) first) first) := by tree_poly
  have hphi : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) first) second) := by tree_poly
  have halpha : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) second) first) := by tree_poly
  have hhit : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) second) second) := by tree_poly
  unfold setupRealizer
  exact polynomial_pair (polynomial_composition polynomial_first polynomial_listLength)
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair hphi halpha) polynomial_twoEntries)
      (polynomial_composition (polynomial_pair (polynomial_constant 0) hQ) polynomial_twoEntries))
      polynomial_twoEntries)
      (polynomial_composition (polynomial_pair
        (polynomial_choose hhit (polynomial_constant 1) (polynomial_constant 0))
        (polynomial_constant 1)) polynomial_twoEntries))

def count (z : Input) : ℕ := (IntegerMatrixPrograms.iterate (setup z)).headD 0

def countRealizer : Realizer count :=
  composition (composition setupRealizer IntegerMatrixPrograms.iterateRealizer) (head 0)

/-- All stored numbers are binary; only the supplied trial marker controls
iteration, so evaluation is polynomial in that marker and binary data. -/
theorem polynomial_count : PolynomialTime countRealizer := by
  have hi : PolynomialTime (composition setupRealizer IntegerMatrixPrograms.iterateRealizer) := by
    obtain ⟨p,hp⟩ := polynomial_setup
    apply work_composition ⟨p,hp⟩ IntegerMatrixPrograms.work_iterate (Polynomial.X+p)
    intro z
    have hl := (list_length_le_weight z.1).trans (weight_fst z)
    have hw := weight_snd (setup z)
    have hc := hp z
    simp only [Polynomial.eval_add,Polynomial.eval_X,setup] at *
    omega
  exact polynomial_composition hi (polynomial_head 0)

def recurrence (Q phi alpha initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | n+1 => phi*recurrence Q phi alpha initial n+alpha*Q^n

private lemma iterate_eq (B : List (List ℕ)) (v : List ℕ) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,(B,v))=
      ((fun v => IntegerMatrixPrograms.propagate (B,v))^[N]) v := by
  induction N generalizing v with
  | zero => rfl
  | succ N ih =>
    rw [IntegerMatrixPrograms.iterate_succ,ih,Function.iterate_succ_apply]

private lemma propagate_two (Q phi alpha x y : ℕ) :
    IntegerMatrixPrograms.propagate ([[phi,alpha],[0,Q]],[x,y])=
      [phi*x+alpha*y,Q*y] := by
  simp [IntegerMatrixPrograms.propagate,IntegerMatrixPrograms.dot_cons,
    IntegerMatrixPrograms.dot_nil,Nat.mul_comm]

lemma count_eq (xs : List Bool) (Q phi alpha : ℕ) (hit : Bool) :
    count (xs,((Q,phi),(alpha,hit)))=
      recurrence Q phi alpha (if hit then 1 else 0) xs.length := by
  have hiter (N initial : ℕ) :
      ((fun v => IntegerMatrixPrograms.propagate ([[phi,alpha],[0,Q]],v))^[N]) [initial,1]=
        [recurrence Q phi alpha initial N,Q^N] := by
    induction N with
    | zero => simp [recurrence]
    | succ N ih =>
      rw [Function.iterate_succ_apply',ih,propagate_two]
      simp only [recurrence,pow_succ]
      rw [Nat.mul_comm Q (Q^N)]
  unfold count setup
  rw [iterate_eq,hiter]
  rfl

lemma recurrence_retry {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (p : IntegerLaw (Option A) Q) (fallback x : A) (N : ℕ) :
    recurrence Q (p.count none) (p.count (some x)) (if x=fallback then 1 else 0) N=
      IntegerLaw.retryCount p fallback N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [recurrence,ih,IntegerLaw.retryCount]
    exact Nat.add_comm _ _

end ContingencyTables.RetryNumeratorPrograms

end OAI
