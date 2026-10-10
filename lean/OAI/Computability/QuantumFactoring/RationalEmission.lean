import Mathlib
import OAI.Computability.QuantumFactoring.QuarterPreparation
import OAI.Computability.QuantumFactoring.EmissionLists
import OAI.Computability.QuantumFactoring.EmissionPolynomialUnary
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Computability.QuantumFactoring.BitStackRationalFloor
import OAI.Computability.QuantumFactoring.BitStackRationalPower

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool}
lemma ratAdd {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x+g x):=(ofProcedure Procedure.ratAdd).comp (hf.pair hg)
lemma ratMul {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x*g x):=(ofProcedure Procedure.ratMul).comp (hf.pair hg)
lemma ratDiv {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x/g x):=(ofProcedure Procedure.ratDiv).comp (hf.pair hg)
lemma ratSub {f g : α→ℚ} (hf : Emits ea ratCode f) (hg : Emits ea ratCode g) :
    Emits ea ratCode (fun x=>f x-g x):=(ofProcedure Procedure.ratSub).comp (hf.pair hg)
lemma ratPow {f : α→ℚ} {k : α→ℕ} (hf : Emits ea ratCode f) (hk : Emits ea unaryCode k) :
    Emits ea ratCode (fun x=>(f x)^(k x)):=(ofProcedure Procedure.ratPow).comp (hk.pair hf)
lemma ratFloor {f : α→ℚ} (hf : Emits ea ratCode f) :
    Emits ea intCode (fun x=>⌊f x⌋):=(ofProcedure Procedure.ratFloor).comp hf
lemma intRat {f : α→ℤ} (hf : Emits ea intCode f) :
    Emits ea ratCode (fun x=>(f x:ℚ)):=(ofProcedure Procedure.intToRat).comp hf
lemma completionCoeff {E : α→ℕ} {z A : α→ℚ} (hE : Emits ea unaryCode E)
    (hz : Emits ea ratCode z) (hA : Emits ea ratCode A) :
    Emits ea ratCode (fun x=>Exactness.completionCoeff (E x) (z x) (A x)):=by
  have htwo:=(const ea ratCode 2).ratPow hE
  exact ((htwo.ratMul (hz.ratDiv hA)).ratFloor.intRat).ratDiv htwo
lemma knownProbability {n : α→ℕ} (hn : Emits ea unaryCode n) :
    Emits ea ratCode (fun x=>Exactness.knownProbability (n x)):=by
  exact ((const ea ratCode 1).ratSub ((const ea ratCode 1).ratDiv
    ((const ea ratCode 2).ratPow hn))).ratPow (hn.unaryPow 10)
lemma quarterRetention {n : α→ℕ} (hn : Emits ea unaryCode n) :
    Emits ea ratCode (fun x=>Quarter.retention (n x)):=by
  exact completionCoeff ((hn.unaryMul hn).unaryAdd (const ea unaryCode 2))
    (const ea ratCode (1/2)) (knownProbability hn)
lemma quarterGuessRetention {n : α→ℕ} (hn : Emits ea unaryCode n) :
    Emits ea ratCode (fun x=>Quarter.guessRetention (n x)):=by
  have ht:=(const ea ratCode 2).ratPow ((hn.unaryMul hn).unaryAdd (const ea unaryCode 1))
  exact ht.ratMul ((const ea ratCode (1/4)).ratSub
    (((knownProbability hn).ratMul (quarterRetention hn)).ratDiv (const ea ratCode 2)))
end ExactQuantumFactoring.BitStackProgram.Emits

end


end OAI
