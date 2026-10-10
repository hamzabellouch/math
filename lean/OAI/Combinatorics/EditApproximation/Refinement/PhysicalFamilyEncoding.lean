import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarCodeBits
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarFamily
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

section Encoding

variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies



 theorem physicalFamilyCode_injective (hM : 1 ≤ M) :
    Function.Injective (physicalFamilyCode (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) := by
  intro first second h
  obtain ⟨hp, h⟩ := Nat.pair_eq_pair.mp h
  obtain ⟨hc, hs⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext (Fin.ext hp) (Prod.ext (Fin.ext hc) (physicalScalarCode_injective hM hs))

 theorem physicalFamilyCode_bound (k : ℕ)
    (hpass : passes + 1 ≤ 2 ^ k) (hcopy : copies + 1 ≤ 2 ^ k)
    (hscalar : ∀ key : PhysicalScalarKey M J N target.length exponent F Q R
        (localOnlineMassBound M P H), physicalScalarCode key < 2 ^ (64 * k + 1))
    (key : Key) : physicalFamilyCode target N P F exponent H Q passes copies key <
      2 ^ (256 * k + 4) := by
  have hk : k ≤ 64 * k + 1 := by omega
  have hp := key.1.isLt.trans_le (hpass.trans (Nat.pow_le_pow_right (by decide) hk))
  have hc := key.2.1.isLt.trans_le (hcopy.trans (Nat.pow_le_pow_right (by decide) hk))
  have hi := natPair_lt_two_pow hc (hscalar key.2.2)
  have ho := natPair_lt_two_pow_scaled hp hi (by decide : 1 ≤ 2)
  change Nat.pair _ (Nat.pair _ _) < _
  convert ho using 1
  congr 1
  omega

end Encoding

end EditApproximation

end OAI
