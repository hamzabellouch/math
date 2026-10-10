import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateTerms

namespace OAI

/-! Concrete raw instructions for private-pair subdivision. -/

namespace ContinuumCoulomb.QuantumPrivate
open QuantumRawExchange

def rawScalar (J : ℚ) : Raw := ((false,false),((0,0),((false,false),J)))
def rawField (i : ℕ) (a : Bool) (J : ℚ) : Raw := ((false,true),((i,0),((a,false),J)))
def rawPair (i j : ℕ) (a b : Bool) (J : ℚ) : Raw := ((true,false),((i,j),((a,b),J)))

def rawTerm (n e : ℕ) (R : ℚ) (x : Raw) (k : Fin 4) : Raw :=
  if k = 0 then rawScalar (weight R x.2.2.2 k)
  else if k = 1 then rawField (n+e) false (weight R x.2.2.2 k)
  else if k = 2 then
    if x.1.1 || x.1.2 then rawPair x.2.1.1 (n+e) x.2.2.1.1 true (weight R x.2.2.2 k)
    else rawField (n+e) true (weight R x.2.2.2 k)
  else if x.1.1 then rawPair x.2.1.2 (n+e) x.2.2.1.2 true (weight R x.2.2.2 k)
    else rawField (n+e) true (weight R x.2.2.2 k)

def rawBlock (n e : ℕ) (R : ℚ) (x : Raw) : List Raw := List.ofFn (rawTerm n e R x)

theorem rawTerm_pack {n m : ℕ} (e : Fin m) (t : QMAXZTerm n) (R J : ℚ) (k : Fin 4) :
    rawTerm n e.val R (pack t J) k = pack (term e t k) (weight R J k) := by
  fin_cases k <;> cases t <;>
    simp [rawTerm,rawScalar,rawField,rawPair,pack,term,old,fresh,
      finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]

theorem rawBlock_length (n e : ℕ) (R : ℚ) (x : Raw) : (rawBlock n e R x).length = 4 := by
  simp [rawBlock]

end ContinuumCoulomb.QuantumPrivate

end OAI
