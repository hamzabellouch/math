import Mathlib
import OAI.Computability.VertexCover.Machines.LCNumber
import OAI.Computability.VertexCover.Machines.FiniteFunction

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.FixedLC

variable {a b : ℕ}
def power (n : ℕ) (I : FixedLC a b) : FixedLC (a^n) (b^n) where
  u := I.u^n
  v := I.v^n
  M := I.M^n
  apos := pow_pos I.apos _
  bpos := pow_pos I.bpos _
  Mpos := pow_pos I.Mpos _
  left := (I.toLC.numberedPower n).left
  right := (I.toLC.numberedPower n).right
  projection := (I.toLC.numberedPower n).projection
 theorem power_toLC (n : ℕ) (I : FixedLC a b) :
    (I.power n).toLC=I.toLC.numberedPower n := rfl

def powerMap (n : ℕ) (maps : Fin n → Map a b) : Map (a^n) (b^n) :=
  fun s => finFunctionFinEquiv (fun i => maps i (finFunctionFinEquiv.symm s i))
def powerRow (hb : 0<b) (n : ℕ) (p : FixedLC a b × ℕ) : Row (a^n) (b^n) :=
  let row := fun i : Fin n => lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)
  ((∑ i, (row i).1.1*p.1.u^i.val,∑ i, (row i).1.2*p.1.v^i.val),
      powerMap n (fun i => (row i).2))

noncomputable def powerRowPoly (_ha : 0<a) (hb : 0<b) (n : ℕ) :
    Poly (prodBits (code (a := a) (b := b)) natBits) rowCode (powerRow hb n) := by
  let enc := prodBits (code (a := a) (b := b)) natBits
  let I := Poly.fst (code (a := a) (b := b)) natBits
  let e := Poly.snd (code (a := a) (b := b)) natBits
  let count := I.comp (MPoly hb)
  let row (i : Fin n) :=
    (I.pair (((e.pair (count.comp (Poly.natPow i.val))).comp Poly.natDiv).pair count |>.comp Poly.natMod)).comp (lookupPoly hb)
  let left := Poly.finiteSum enc (fun p (i : Fin n) =>
      (lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)).1.1*p.1.u^i.val)
    (fun i => ((((row i).comp (Poly.fst (prodBits natBits natBits) mapCode)).comp
      (Poly.fst natBits natBits)).pair ((I.comp uPoly).comp (Poly.natPow i.val)) |>.comp Poly.natMul))
  let right := Poly.finiteSum enc (fun p (i : Fin n) =>
      (lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)).1.2*p.1.v^i.val)
    (fun i => ((((row i).comp (Poly.fst (prodBits natBits natBits) mapCode)).comp
      (Poly.snd natBits natBits)).pair ((I.comp vPoly).comp (Poly.natPow i.val)) |>.comp Poly.natMul))
  let maps := Poly.finFunction enc n (fun p i => (lookup hb (p.1,p.2/p.1.M^i.val%p.1.M)).2)
    (fun i => (row i).comp (Poly.snd (prodBits natBits natBits) mapCode))
  exact (left.pair right).pair (maps.comp (Poly.finite _ _ (finiteCode_injective _) (powerMap n)))
 theorem powerRow_correct (hb : 0<b) (n : ℕ) (I : FixedLC a b) (e : Fin (I.power n).M) :
    powerRow hb n (I,e.val)=(((I.power n).left e |>.val,(I.power n).right e |>.val),
      (I.power n).projection e) := by
  have he (i : Fin n) :
      lookup hb (I,e.val/I.M^i.val%I.M) =
        (((I.left (finFunctionFinEquiv.symm e i)).val,
          (I.right (finFunctionFinEquiv.symm e i)).val),I.projection (finFunctionFinEquiv.symm e i)) :=
    lookup_valid hb I (finFunctionFinEquiv.symm e i)
  simp only [powerRow,he]
  rfl
noncomputable def powerPoly (ha : 0<a) (hb : 0<b) (n : ℕ) :
    Poly (code (a := a) (b := b)) code (power n) :=
  materializePoly code (one ha hb) (power n) (pow_pos hb _)
    (uPoly.comp (Poly.natPow n)) (vPoly.comp (Poly.natPow n))
    ((MPoly hb).comp (Poly.natPow n)) (powerRowPoly ha hb n)
    (powerRow_correct hb n)
end VertexCover.Machine.FixedLC
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
