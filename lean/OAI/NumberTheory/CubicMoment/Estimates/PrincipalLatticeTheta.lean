import OAI.NumberTheory.CubicMoment.Estimates.ResidueGaussianScale

namespace OAI

/-! Poisson inversion of the principal lattice Gaussian, with its zero
term retained. This supplies the pole term of the principal ideal zeta
function rather than treating it as a nonprincipal Hecke function. -/
noncomputable section
namespace CubicFirstMoment

def principalLatticeTheta (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)

lemma principalLatticeTheta_inversion {t : ℝ} (ht : 0 < t) :
    principalLatticeTheta t=(1/t:ℝ)*principalLatticeTheta (1/t) := by
  have hA := residueHeckeScale_pos (q := 1) one_ne_zero
  let F := radialGaussianSchwartz (t/residueHeckeScale 1) (div_pos ht hA)
  have hp := poisson_eisenstein_coset F (1:ℂ) one_ne_zero 0
  have he (a : Eisenstein) : F (a:ℂ)=
      (Real.exp (-norm a*t/residueHeckeScale 1):ℂ) := by
    dsimp only [F]
    rw [radialGaussianSchwartz_apply]
    change (Real.exp (-(t/residueHeckeScale 1)*‖(a:ℂ)‖^2):ℂ)=
      (Real.exp (-Complex.normSq (a:ℂ)*t/residueHeckeScale 1):ℂ)
    rw [Complex.normSq_eq_norm_sq]
    congr 2
    ring
  have hf := residueGaussian_prefactor (q := 1) one_ne_zero ht
  norm_num only [norm,Eisenstein.coe_one,Complex.normSq_one,Real.sqrt_one,one_mul,mul_one] at hf
  have hx (a : Eisenstein) := residueGaussian_exponent (q := 1) one_ne_zero ht a
  simp only [Eisenstein.coe_one,one_mul] at hx
  simp only [one_mul,zero_add,Complex.normSq_one,mul_one,tracePair,zero_mul,
    Complex.zero_re,mul_zero,AddChar.map_zero_eq_one,Circle.coe_one,he] at hp
  dsimp only [F] at hp
  simp_rw [radialGaussianSchwartz_traceFourier,hx] at hp
  rw [tsum_mul_left,Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,hf] at hp
  calc
    principalLatticeTheta t=(1/t:ℝ)*
        ∑' a : Eisenstein, (Real.exp (-norm a/(residueHeckeScale 1*t)):ℂ) := hp
    _ = _ := by
      congr 1
      apply tsum_congr
      intro a
      congr 2
      ring

end CubicFirstMoment

end

end OAI
