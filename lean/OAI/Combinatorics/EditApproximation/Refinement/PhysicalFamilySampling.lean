import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarFamilyLaw
import OAI.Combinatorics.EditApproximation.Probability.RejectionSelectedLaw
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The finite scalar family is exactly the accepted output of the
independent literal rejection samplers. Only requested coordinates need
be generated; their failure counts have a product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)





 theorem physicalFamilyLaw_eq_rejectionAcceptedLaw :
    physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies =
      rejectionAcceptedLaw (physicalFamilyRange (M := M) (J := J) (R := R)
        target N P F exponent H Q passes copies) := rfl

 theorem physicalFamily_rejection_runtime_law :
    (rejectionRuntimeArrayLaw (physicalFamilyRange (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)).map Prod.snd =
    physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies :=
  rejectionRuntimeArrayLaw_accepted _

omit [NeZero M] in
 theorem physicalFamilyRange_bits_le (bits : ℕ)
    (hM : M ≤ 2 ^ bits) (hB : localOnlineMassBound M P H ≤ 2 ^ bits)
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    rejectionBitCount (physicalFamilyRange target N P F exponent H Q passes copies key) ≤ bits := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  rcases key with ⟨pass, copy, scalar, index⟩
  cases scalar with
  | inl online =>
    change online.2.val.val ≤ 2 ^ bits
    exact (Nat.le_of_lt_succ online.2.val.isLt).trans hB
  | inr group => exact hM

end Family

end EditApproximation

end OAI
