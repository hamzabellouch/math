import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierCRT

namespace OAI

/-! Exact unramified factorization of the Eisenstein-row Fourier coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_factor {u c : Eisenstein}
    (hu : primary u) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0) (hcu : IsCoprime c u)
    (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (u*c) h=
      (cubicSymbol u (3*c)*cubicSymbol u c)*cubicThetaSymbolFourier u (primary_ne_zero hu) h*
        cubicThetaEisensteinGaussCoefficient c h := by
  have hu0 := primary_ne_zero hu
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  have huc : IsCoprime u (3*c) := by
    have h3 := isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
    exact h3.symm.mul_right hcu.symm
  have h3uc : (3:Eisenstein) ∣ u*c := dvd_mul_of_dvd_right hc u
  have hq : u*(3*c)=3*(u*c) := by ring
  let : Finite (Residues u) := finite_residues hu0
  let : Finite (Residues (3*c)) := finite_residues h3c
  let : Finite (Residues (u*(3*c))) := finite_residues (mul_ne_zero hu0 h3c)
  let : Fintype (Residues u) := Fintype.ofFinite _
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  let : Fintype (Residues (u*(3*c))) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix u (3*c)) (residueMix_bijective hu0 h3c huc)
  let F (x : Residues (u*(3*c))) : ℂ :=
    cubicThetaEisensteinWeight (u*c) (residueRepresentative (u*(3*c)) x)*
      residueFourierChar (u*(3*c)) (mul_ne_zero hu0 h3c)
        (Ideal.Quotient.mk (modulus (u*(3*c))) h*x)
  let f (x : Residues u) : ℂ := cubicSymbol u (residueRepresentative u x)*
    residueFourierChar u hu0 (Ideal.Quotient.mk (modulus u) h*x)
  let g (y : Residues (3*c)) : ℂ := cubicThetaEisensteinWeight c (residueRepresentative (3*c) y)*
    residueFourierChar (3*c) h3c (Ideal.Quotient.mk (modulus (3*c)) h*y)
  let C : ℂ := cubicSymbol u (3*c)*cubicSymbol u c
  have hF (v : Residues u × Residues (3*c)) : F (e v)=C*(f v.1*g v.2) := by
    have hr : Ideal.Quotient.mk (modulus (u*(3*c)))
        (residueRepresentative (u*(3*c)) (e v))=
      Ideal.Quotient.mk (modulus (u*(3*c)))
        ((3*c)*residueRepresentative u v.1+u*residueRepresentative (3*c) v.2) :=
      residueRepresentative_spec _ _
    have hw := cubicThetaEisensteinWeight_congr_of_eq h3uc hq hr
    dsimp only [F,f,g,C]
    rw [hw,cubicThetaEisensteinWeight_mix hu hc hcu]
    change _*residueFourierChar (u*(3*c)) (mul_ne_zero hu0 h3c)
      (Ideal.Quotient.mk (modulus (u*(3*c))) h*residueMix u (3*c) v)=_
    rw [residueFourierChar_mix hu0 h3c]
    ring
  rw [cubicThetaEisensteinGaussCoefficient_fourier_of_eq (mul_ne_zero hu0 hc0)
    (mul_ne_zero hu0 h3c) hq]
  change (∑' x, F x)=C*cubicThetaSymbolFourier u hu0 h*cubicThetaEisensteinGaussCoefficient c h
  rw [← e.tsum_eq]
  simp_rw [hF]
  rw [tsum_fintype,Fintype.sum_prod_type]
  rw [cubicThetaEisensteinGaussCoefficient_fourier hc0]
  change (∑ x : Residues u, ∑ y : Residues (3*c), C*(f x*g y))=
    C*(∑' x : Residues u, f x)*(∑' y : Residues (3*c), g y)
  rw [tsum_fintype,tsum_fintype]
  calc
    _ = ∑ x : Residues u, (C*f x)*(∑ y : Residues (3*c), g y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (∑ x : Residues u, C*f x)*(∑ y : Residues (3*c), g y) :=
      (Finset.sum_mul ..).symm
    _ = _ := by congr 1; rw [Finset.mul_sum]

end CubicFirstMoment

end

end OAI
