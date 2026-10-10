import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanFourierGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCharacter

namespace OAI

/-! Exact unit change of variables in the actual Kloosterman kernel.
The multiplier is the cubic character from the Eisenstein row weight. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaFiniteKloosterman_unit_scale {c u : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hu : primary u) (hcu : IsCoprime c u)
    (h k : Residues (3*c)) :
    cubicThetaFiniteKloosterman c hc0 h k=
      cubicSymbol u c*cubicThetaFiniteKloosterman c hc0
        (h*Ideal.Quotient.mk (modulus (3*c)) u)
        (k*Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) u)) := by
  have h3u := isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
  have hU := residue_isUnit_of_isCoprime (h3u.mul_left hcu)
  let U : (Residues (3*c))ˣ := hU.unit
  have hUv : (U : Residues (3*c))=Ideal.Quotient.mk (modulus (3*c)) u := hU.unit_spec
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  unfold cubicThetaFiniteKloosterman
  rw [tsum_fintype,tsum_fintype]
  calc
    _ = ∑ x : Residues (3*c),cubicThetaEisensteinResidueWeight c ((U:Residues (3*c))*x)*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0)
          (h*((U:Residues (3*c))*x)+k*Ring.inverse ((U:Residues (3*c))*x)) :=
      (Equiv.sum_comp U.mulLeft _).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [hUv,cubicThetaEisensteinResidueWeight_mul hc hu hcu,
        Ring.inverse_mul (Or.inl hU)]
      have he : h*(Ideal.Quotient.mk (modulus (3*c)) u*x)+
          k*(Ring.inverse x*Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) u))=
          (h*Ideal.Quotient.mk (modulus (3*c)) u)*x+
            (k*Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) u))*Ring.inverse x := by ring
      rw [he]
      ring

theorem cubicThetaKloostermanSum_unit_scale {c u : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hu : primary u) (hcu : IsCoprime c u)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum h (u*k) c hc=
      cubicSymbol u c*cubicThetaKloostermanSum (u*h) k c hc := by
  rw [←cubicThetaFiniteKloosterman_integer h (u*k) hc hc0,
    ←cubicThetaFiniteKloosterman_integer (u*h) k hc hc0,
    cubicThetaFiniteKloosterman_unit_scale hc hc0 hu hcu]
  have h3u := isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
  have hU := residue_isUnit_of_isCoprime (h3u.mul_left hcu)
  rw [map_mul,map_mul,mul_comm (Ideal.Quotient.mk (modulus (3*c)) u)
    (Ideal.Quotient.mk (modulus (3*c)) k),mul_assoc,
    Ring.mul_inverse_cancel _ hU,mul_one,
    mul_comm (Ideal.Quotient.mk (modulus (3*c)) h)]

end CubicFirstMoment

end

end OAI
