import OAI.Combinatorics.ContingencyTables.Counting.CountingAmplifiedProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport
import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicInputBounds

namespace OAI

/-! # Exact law and public word budget of outer confidence repetition -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS GridBoundary CommonBasesFPRAS FiniteObservableTransport Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section

variable (single : Input→TreeFraction.Fraction) (width : Request→ℕ)

theorem sameLaw (req : Request) (hw : 0 < width req) (K : ℕ) (g : (Fin K→Bool)→ℚ)
    (hs : SameLaw (fun bits : Fin (width req)→Bool => TreeFraction.val (single (req,List.ofFn bits))) g) :
    SameLaw (fun bits : Fin (budget width req)→Bool =>
      TreeFraction.val (output single width (req,List.ofFn bits)))
      (fun bits : Fin (repeats req*K)→Bool =>
        rationalMedian (List.ofFn (fun i => g (gridWordEquiv (repeats req) K bits i)))) := by
  let R := repeats req
  let f := fun bits : Fin (width req)→Bool => TreeFraction.val (single (req,List.ofFn bits))
  have hp := (hs.independent R).map (fun xs : Fin R→ℚ => rationalMedian (List.ofFn xs))
  intro phi
  have hleft := uniformAverage_equiv (gridWordEquiv R (width req))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => f (xs i)))))
  have hright := uniformAverage_equiv (gridWordEquiv R K)
    (fun xs => phi (rationalMedian (List.ofFn (fun i => g (xs i)))))
  have hout : uniformAverage (fun bits : Fin (budget width req)→Bool =>
      phi (TreeFraction.val (output single width (req,List.ofFn bits)) ))=
      uniformAverage (fun bits : Fin (R*width req)→Bool =>
        phi (rationalMedian (List.ofFn (fun i => f (gridWordEquiv R (width req) bits i))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (output_ofFn single width req hw bits)
  exact hout.trans (hleft.trans ((hp phi).trans hright.symm))

variable {m n : ℕ}

lemma repeats_request (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (hd : 0 < delta) :
    repeats (CountingDirectProgram.request r c b epsilon delta)=repetitionCount delta := by
  change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
  rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]

def budgetPolynomial (p : Polynomial ℕ) : Polynomial ℕ := 64*X*p

lemma budget_bound (p : Polynomial ℕ)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (hd : 0 < delta)
    (hw : width (CountingDirectProgram.request r c b epsilon delta) ≤ p.eval (size r c b epsilon delta)) :
    budget width (CountingDirectProgram.request r c b epsilon delta) ≤
      (budgetPolynomial p).eval (size r c b epsilon delta) := by
  unfold budget
  rw [repeats_request r c b epsilon delta hd]
  simpa only [budgetPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    CommonBasesFPRAS.repetitionCount]
    using Nat.mul_le_mul (repeats_le r c b epsilon delta) hw

end
end ContingencyTables.CountingAmplifiedProgram

end OAI
