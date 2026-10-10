import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanInvolution
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKloostermanInflation

namespace OAI

/-! Hermitian inversion for the unramified local Kloosterman factor,
including its common-factor zeros. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaResidueSymbol_inverse {u : Eisenstein} (hu : primary u)
    (x : Residues u) :
    cubicSymbol u (residueRepresentative u (cubicThetaResidueInversePerm u x))=
      star (cubicSymbol u (residueRepresentative u x)) := by
  by_cases hx : IsUnit x
  · have hi := cubicThetaResidueInversePerm_of_isUnit u x hx
    have hc : IsCoprime u (residueRepresentative u x) := by
      apply isCoprime_of_residue_isUnit
      rwa [residueRepresentative_spec]
    have hr : Ideal.Quotient.mk (modulus u)
        (residueRepresentative u (Ring.inverse x)*residueRepresentative u x)=
        Ideal.Quotient.mk (modulus u) 1 := by
      rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,map_one,
        Ring.inverse_mul_cancel x hx]
    have he := cubicSymbol_congr hr
    rw [cubicSymbol_mul_upper hu] at he
    have hnorm : cubicSymbol u (residueRepresentative u x)*
        star (cubicSymbol u (residueRepresentative u x))=1 := by
      rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hu hc]
      norm_num
    have hone : cubicSymbol u 1=1 := by simpa using cubicSymbol_pow_upper hu 1 0
    rw [hone] at he
    rw [hi]
    have hn : cubicSymbol u (residueRepresentative u x)≠0 := by
      intro hz
      rw [hz,zero_mul] at hnorm
      exact zero_ne_one hnorm
    apply mul_right_cancel₀ hn
    exact he.trans (by simpa only [mul_comm] using hnorm.symm)
  · have hi := cubicThetaResidueInversePerm_of_not_isUnit u x hx
    rw [hi,cubicThetaSymbol_nonunit_zero hu x hx,star_zero]

theorem cubicThetaSymbolKloosterman_hermitian {u : Eisenstein} (hu : primary u)
    (h k : Residues u) :
    cubicThetaSymbolKloosterman u (primary_ne_zero hu) h k=
      star (cubicThetaSymbolKloosterman u (primary_ne_zero hu) (-k) (-h)) := by
  let : Finite (Residues u) := finite_residues (primary_ne_zero hu)
  let : Fintype (Residues u) := Fintype.ofFinite _
  unfold cubicThetaSymbolKloosterman
  rw [tsum_fintype,tsum_fintype,star_sum]
  calc
    _ = ∑ x : Residues u,cubicSymbol u (residueRepresentative u (cubicThetaResidueInversePerm u x))*
      residueFourierChar u (primary_ne_zero hu)
        (h*cubicThetaResidueInversePerm u x+k*Ring.inverse (cubicThetaResidueInversePerm u x)) :=
      ((cubicThetaResidueInversePerm u).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : IsUnit x
      · have hi := cubicThetaResidueInversePerm_of_isUnit u x hx
        rw [cubicThetaResidueSymbol_inverse hu,hi,Ring.inverse_inverse hx,
          star_mul,cubicThetaResidueFourier_star]
        rw [mul_comm (star (cubicSymbol u (residueRepresentative u x)))]
        congr 1
        congr 1
        ring
      · have hi := cubicThetaResidueInversePerm_of_not_isUnit u x hx
        rw [hi,cubicThetaSymbol_nonunit_zero hu x hx,zero_mul,zero_mul,star_zero]

theorem cubicThetaPrimeKloosterman_support_left {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein)
    (hK : cubicThetaSymbolKloosterman (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*h))
      (Ideal.Quotient.mk (modulus (p^(n+1))) k)≠0) : p^n∣k := by
  have hprim : primary (p^(n+1)) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  have he := cubicThetaSymbolKloosterman_hermitian hprim
    (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*h))
    (Ideal.Quotient.mk (modulus (p^(n+1))) k)
  have hn : cubicThetaSymbolKloosterman (p^(n+1)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+1))) (-k))
      (Ideal.Quotient.mk (modulus (p^(n+1))) (p^n*(-h)))≠0 := by
    intro hz
    apply hK
    rw [he]
    have hm : p^n*(-h)=-(p^n*h) := by ring
    rw [hm,map_neg,map_neg] at hz
    rw [hz,star_zero]
  have hd := cubicThetaPrimeKloosterman_support hp n (-k) (-h) hn
  exact dvd_neg.mp hd

end CubicFirstMoment

end

end OAI
