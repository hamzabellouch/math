import OAI.LinearAlgebra.CirculantHadamard.CyclicNorm
import OAI.LinearAlgebra.CirculantHadamard.BinaryEvaluation
import OAI.LinearAlgebra.CirculantHadamard.BinaryLocalFamily
import OAI.LinearAlgebra.CirculantHadamard.AlternatingTorsion

namespace OAI

noncomputable section

namespace CirculantHadamard

open CyclicRing BinaryEvaluation

/-- The binary contradiction starts with the original integer sign row and
its full cyclic norm equation. -/
theorem binary_sign_norm_impossible {u : ℕ} [NeZero u]
    (hu : 1 < u) (hodd : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    False := by
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hodd f)
  have hH : BinaryCoefficients.Signs (fun j => (H j).coeff) :=
    BinaryBlocks.crt_blocks_signs hodd f hsign
  obtain ⟨hc, hd, hg⟩ := gaussian_norms_of_cyclic_norm hodd f hsign hnorm
  apply BinaryLocalFamily.contradiction_of_evaluated_data u hu0 hodd
    (cG H) (dG H) (gG H) hc hd hg
    (aValue u hu0 H) (bValue u hu0 H) (UValue u hu0 H)
  · exact fun S => cValue_eq u hu0 H S
  · exact fun S => dValue_eq u hu0 H S
  · exact fun S => gValue_eq u hu0 hH S
  · exact alternatingProduct_odd_torsion u hu hodd (cG H)
      (by simpa only [Nat.cast_pow] using hc)
  · exact alternatingProduct_odd_torsion u hu hodd (dG H)
      (by simpa only [Nat.cast_pow] using hd)
  · exact alternatingProduct_odd_torsion u hu hodd (gG H)
      (by simpa only [Nat.cast_pow] using hg)

/-- No real circulant sign Hadamard matrix has order `4u²` for odd `u > 1`.
The original real-matrix predicate is converted by the proved integer-row
equivalence; every subsequent construction is made from that actual row. -/
theorem not_exists_four_mul_odd_square {u : ℕ}
    (hu : 1 < u) (hodd : Odd u) :
    ¬ ExistsRealCirculantHadamard (4 * u ^ 2) := by
  let : NeZero u := ⟨(lt_trans Nat.zero_lt_one hu).ne'⟩
  intro hH
  obtain ⟨f, hsign, hnorm⟩ :=
    (exists_cyclicSignRow_iff_real (n := 4 * u ^ 2)).mpr hH
  exact binary_sign_norm_impossible hu hodd f hsign hnorm

end CirculantHadamard

end

end OAI
