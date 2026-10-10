import Mathlib
import OAI.Computability.QuantumFactoring.BitStackRationals

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def ratFloor : Procedure ratCode intCode (fun q=>⌊q⌋):=by
  let num:=ratNum
  let den:=ratDen
  let mag:=intAbs.comp num
  let negmag:=binaryAdd.comp ((binaryDiv.comp
    ((binarySub.comp (mag.pair (constant ratCode Nat.bits 1))).pair den)).pair
    (constant ratCode Nat.bits 1))
  let pos:=natToInt.comp (binaryDiv.comp (mag.pair den))
  let neg:=intNeg.comp (natToInt.comp negmag)
  exact (conditional (intSign.comp num) neg pos).congrFun (by
    intro q
    change (if decide (q.num<0) then -((((q.num.natAbs-1)/q.den+1):ℕ):ℤ)
      else ((q.num.natAbs/q.den):ℤ))=⌊q⌋
    rw [Rat.floor_def']
    obtain ⟨d,hd⟩:=Nat.exists_eq_succ_of_ne_zero q.den_nz
    rw [hd]
    cases q.num with
    | ofNat a=>simp
    | negSucc a=>
      simp only [Int.negSucc_lt_zero, decide_true, ite_true, Int.natAbs_negSucc,
        Int.negSucc_ediv_ofNat_succ]
      change -((((a+1-1)/(d+1)+1):ℕ):ℤ)=Int.negSucc (a/(d+1))
      simp only [Nat.add_sub_cancel]
      rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
