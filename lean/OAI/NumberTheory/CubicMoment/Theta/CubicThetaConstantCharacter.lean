import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds

namespace OAI

/-! Character orthogonality for the constant Fourier coefficient, on
the actual subgroup of primary residue classes modulo 3c. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_mul {u c : Eisenstein} (hu : primary u)
    (hcu : IsCoprime c u) (d : Eisenstein) :
    cubicThetaEisensteinWeight c (u*d) = cubicSymbol u c*cubicThetaEisensteinWeight c d := by
  have hp : primary (u*d) ↔ primary d := by
    rw [primary_iff_residue_one, primary_iff_residue_one, map_mul,
      (primary_iff_residue_one u).mp hu, one_mul]
  have hg : IsCoprime c (u*d) ↔ IsCoprime c d := by
    rw [IsCoprime.mul_right_iff, and_iff_right hcu]
  unfold cubicThetaEisensteinWeight
  rw [hp,hg]
  split_ifs with hd
  · exact cubicSymbol_mul_lower (primary_ne_zero hu) (primary_ne_zero hd.1) c
  · simp

lemma cubicThetaEisensteinResidueWeight_mul {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hu : primary u) (hcu : IsCoprime c u)
    (x : Residues (3*c)) :
    cubicThetaEisensteinResidueWeight c (Ideal.Quotient.mk (modulus (3*c)) u*x) =
      cubicSymbol u c*cubicThetaEisensteinResidueWeight c x := by
  calc
    _ = cubicThetaEisensteinResidueWeight c
        (Ideal.Quotient.mk (modulus (3*c)) (u*residueRepresentative (3*c) x)) := by
      rw [map_mul, residueRepresentative_spec]
    _ = cubicThetaEisensteinWeight c (u*residueRepresentative (3*c) x) :=
      cubicThetaEisensteinResidueWeight_mk hc _
    _ = _ := cubicThetaEisensteinWeight_mul hu hcu _

theorem cubicThetaEisenstein_constant_vanish {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c ≠ 0) (hu : primary u)
    (hcu : IsCoprime c u) (hchi : cubicSymbol u c ≠ 1) :
    cubicThetaEisensteinGaussCoefficient c 0 = 0 := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3u : IsCoprime (3:Eisenstein) u :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
  have hU := residue_isUnit_of_isCoprime (h3u.mul_left hcu)
  let U : (Residues (3*c))ˣ := hU.unit
  have hUv : (U : Residues (3*c)) = Ideal.Quotient.mk (modulus (3*c)) u := hU.unit_spec
  have he : (∑ x : Residues (3*c), cubicThetaEisensteinResidueWeight c x) =
      cubicSymbol u c*∑ x : Residues (3*c), cubicThetaEisensteinResidueWeight c x := by
    calc
      _ = ∑ x : Residues (3*c), cubicThetaEisensteinResidueWeight c ((U:Residues (3*c))*x) :=
        (Equiv.sum_comp U.mulLeft _).symm
      _ = _ := by
        simp_rw [hUv, cubicThetaEisensteinResidueWeight_mul hc hu hcu]
        rw [Finset.mul_sum]
  have hz := eq_zero_of_mul_eq_self_left hchi he.symm
  simpa [cubicThetaEisensteinGaussCoefficient, tracePair, tsum_fintype] using hz

end CubicFirstMoment

end

end OAI
