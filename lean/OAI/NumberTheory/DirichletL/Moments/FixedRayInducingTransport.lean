import OAI.NumberTheory.DirichletL.Moments.ExceptionalPair
import OAI.NumberTheory.DirichletL.Moments.FixedRowMask

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRayInducingTransport
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile
open CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentExceptionalPair CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O

theorem modulus_generator_ne_zero (ν : Character) :
    idealGenerator ν.modulus ≠ 0 :=
  idealGenerator_ne_zero ν.modulus ν.modulus_ne_bot

theorem modulus_unit_iff (ν : Character) (n : O) :
    IsUnit (Ideal.Quotient.mk ν.modulus n) ↔
      IsCoprime n (idealGenerator ν.modulus) := by
  rw [IdealCharacter.isUnit_mk_iff_isCoprime]
  conv_lhs => rw [←span_idealGenerator ν.modulus]
  rw [Ideal.isCoprime_span_singleton_iff]

theorem elementCoeff_product_inverse_mask (η ν : Character) (n : O) :
    elementCoeff ((η.product ν).product ν.inverse) n =
      if IsCoprime n (idealGenerator ν.modulus) then elementCoeff η n else 0 := by
  rw [elementCoeff_product,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsCoprime n (idealGenerator ν.modulus)
  · have hv : elementCoeff ν n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr ((modulus_unit_iff ν n).mpr hn)
    simp only [hn,ite_true,mul_assoc,mul_inv_cancel₀ hv,mul_one]
  · have hv : elementCoeff ν n = 0 :=
      MulChar.map_nonunit ν.residue (fun hu=>hn ((modulus_unit_iff ν n).mp hu))
    simp only [hn,ite_false,hv,mul_zero,zero_mul]

theorem rowTwist_product (η ν : Character) (m f z n : O) :
    rowTwist (elementHom (η.product ν)) m f z n =
      rowTwist (elementHom η) m f z n * elementCoeff ν n := by
  change elementCoeff (η.product ν) n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) * elementCoeff ν n
  rw [elementCoeff_product]
  ring

theorem rowTwist_product_inverse_mask (η ν : Character) (m A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom ((η.product ν).product ν.inverse)) m 1 (A*z) n =
      rowTwist (elementHom η) (m*idealGenerator ν.modulus) 1 (A*z) n := by
  rw [row_mask_mul η m (idealGenerator ν.modulus) A z n hmLam hm2]
  change elementCoeff ((η.product ν).product ν.inverse) n *
    idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n}) = _
  rw [elementCoeff_product_inverse_mask]
  split_ifs
  · rfl
  · exact zero_mul _

theorem fixedInducingRow_product_of (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (h : FixedInducingRow η Q m A z) :
    FixedInducingRow (η.product ν) Q m A z :=
  fixedInducingRow_of_product η (η.product ν) ν Q m A z z hν
    (fun n=>rowTwist_product η ν m 1 (A*z) n) h

theorem fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν) Q m A z ↔ FixedInducingRow η Q m A z := by
  constructor
  · intro h
    have hi := fixedInducingRow_product_of (η.product ν) ν.inverse Q m A z hν h
    obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hi
    apply (fixedInducingRow_mul_mask_iff η Q m (idealGenerator ν.modulus) A z
      hm (modulus_generator_ne_zero ν) hA hz hmLam hm2).mp
    exact ⟨χ,ψ,hprim,hind,hQ,fun n=>(hrow n).trans
      (rowTwist_product_inverse_mask η ν m A z n hmLam hm2)⟩
  · exact fixedInducingRow_product_of η ν Q m A z hν

theorem not_fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_iff η ν Q m A z hν hm hA hz hmLam hm2)

theorem fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν.inverse) Q m A z ↔ FixedInducingRow η Q m A z :=
  fixedInducingRow_product_iff η ν.inverse Q m A z hν hm hA hz hmLam hm2

theorem not_fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν.inverse) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_inverse_iff η ν Q m A z hν hm hA hz hmLam hm2)

end SevenEighths.CenteredMomentFixedRayInducingTransport

end

end OAI
