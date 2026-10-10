import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCharacter

namespace OAI

/-! The finite arithmetic Fourier coefficient under a primary change of
additive frequency. The relation is proved on the actual residue ring;
it is independent of any continuation or theta coefficient formula. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_mul {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0) (hu : primary u)
    (hcu : IsCoprime c u) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c (h*u)=
      star (cubicSymbol u c)*cubicThetaEisensteinGaussCoefficient c h := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3u : IsCoprime (3:Eisenstein) u :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
  obtain ⟨U,hU⟩ := residue_isUnit_of_isCoprime (h3u.mul_left hcu)
  let f (x : Residues (3*c)) : ℂ := cubicThetaEisensteinResidueWeight c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      ((h:ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ)
  let g (x : Residues (3*c)) : ℂ := cubicThetaEisensteinResidueWeight c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      (((h*u:Eisenstein):ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ)
  have he (x : Residues (3*c)) :
      Ideal.Quotient.mk (modulus (3*c)) (residueRepresentative (3*c) (U.mulLeft x))=
        Ideal.Quotient.mk (modulus (3*c)) (u*residueRepresentative (3*c) x) := by
    rw [residueRepresentative_spec,map_mul,residueRepresentative_spec]
    change (U:Residues (3*c))*x=Ideal.Quotient.mk (modulus (3*c)) u*x
    rw [hU]
  have ht (x : Residues (3*c)) : f (U.mulLeft x)=cubicSymbol u c*g x := by
    dsimp only [f,g]
    have hw : cubicThetaEisensteinResidueWeight c (U.mulLeft x)=
        cubicSymbol u c*cubicThetaEisensteinResidueWeight c x := by
      change cubicThetaEisensteinResidueWeight c ((U:Residues (3*c))*x)=_
      rw [hU,cubicThetaEisensteinResidueWeight_mul hc hu hcu]
    rw [hw,tracePhase_congr (mul_ne_zero (by norm_num) hc0) h (he x)]
    have hp : tracePair ((u*residueRepresentative (3*c) x:Eisenstein):ℂ)
        ((h:ℂ)/((3*c:Eisenstein)*traceLambda))=
        tracePair (residueRepresentative (3*c) x:ℂ)
          (((h*u:Eisenstein):ℂ)/((3*c:Eisenstein)*traceLambda)) := by
      unfold tracePair
      congr 2
      push_cast
      ring
    rw [hp]
    ring
  have hs : (∑ x : Residues (3*c), f x)=cubicSymbol u c*∑ x : Residues (3*c), g x := by
    rw [← Equiv.sum_comp U.mulLeft f]
    simp_rw [ht]
    rw [Finset.mul_sum]
  have hunit : star (cubicSymbol u c)*cubicSymbol u c=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hu hcu.symm]
    norm_num
  change (∑' x : Residues (3*c), g x)=star (cubicSymbol u c)*∑' x : Residues (3*c), f x
  rw [tsum_fintype,tsum_fintype,hs,← mul_assoc,hunit,one_mul]

theorem cubicThetaEisensteinGaussCoefficient_cubeFrequency {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0) (hu : primary u)
    (hcu : IsCoprime c u) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c (h*u^3)=cubicThetaEisensteinGaussCoefficient c h := by
  have hp : primary (u^3) := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using primary_mul (primary_mul hu hu) hu
  have hcp : IsCoprime c (u^3) := hcu.pow_right
  rw [cubicThetaEisensteinGaussCoefficient_mul hc hc0 hp hcp]
  have hchi : cubicSymbol (u^3) c=1 := by
    rw [show u^3=u*u*u by ring,cubicSymbol_mul_lower
      (mul_ne_zero (primary_ne_zero hu) (primary_ne_zero hu)) (primary_ne_zero hu),
      cubicSymbol_mul_lower (primary_ne_zero hu) (primary_ne_zero hu)]
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using cubicSymbol_cube_of_isCoprime hu c hcu.symm
  rw [hchi,star_one,one_mul]

end CubicFirstMoment

end

end OAI
