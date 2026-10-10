import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanCRTPhase
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanFourierGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanInversion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussFactor

namespace OAI

/-! Exact coprime factorization of the Kloosterman kernel from the
positive Gram expansion. Both local inverse-square twists and all
common-factor zeros are retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaSymbolKloosterman (u : Eisenstein) (hu0 : u≠0)
    (h k : Residues u) : ℂ :=
  ∑' x : Residues u,cubicSymbol u (residueRepresentative u x)*
    residueFourierChar u hu0 (h*x+k*Ring.inverse x)

lemma cubicThetaKloostermanSum_finite_of_eq (h k : Eisenstein)
    {q c : Eisenstein} (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hq : q≠0)
    (he : q=3*c) :
    cubicThetaKloostermanSum h k c hc=
      ∑' x : Residues q,cubicThetaEisensteinWeight c (residueRepresentative q x)*
        residueFourierChar q hq (Ideal.Quotient.mk (modulus q) h*x+
          Ideal.Quotient.mk (modulus q) k*Ring.inverse x) := by
  subst q
  exact cubicThetaKloostermanSum_finite h k hc hc0

lemma cubicThetaSymbol_nonunit_zero {u : Eisenstein} (hu : primary u)
    (x : Residues u) (hx : ¬IsUnit x) : cubicSymbol u (residueRepresentative u x)=0 := by
  apply cubicSymbol_eq_zero_of_not_isCoprime hu
  intro hc
  have he := residue_isUnit_of_isCoprime hc
  rw [residueRepresentative_spec] at he
  exact hx he

theorem cubicThetaKloostermanSum_factor {u c : Eisenstein}
    (hu : primary u) (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (hcu : IsCoprime c u)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum h k (u*c) (dvd_mul_of_dvd_right hc u)=
      (cubicSymbol u (3*c)*cubicSymbol u c)*
        cubicThetaSymbolKloosterman u (primary_ne_zero hu)
          (Ideal.Quotient.mk (modulus u) h)
          (Ideal.Quotient.mk (modulus u) k*
            (Ring.inverse (Ideal.Quotient.mk (modulus u) (3*c)))^2)*
        cubicThetaFiniteKloosterman c hc0 (Ideal.Quotient.mk (modulus (3*c)) h)
          (Ideal.Quotient.mk (modulus (3*c)) k*
            (Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) u))^2) := by
  have hu0 := primary_ne_zero hu
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  have huc : IsCoprime u (3*c) := by
    have h3 := isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
    exact h3.symm.mul_right hcu.symm
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
        (Ideal.Quotient.mk (modulus (u*(3*c))) h*x+
          Ideal.Quotient.mk (modulus (u*(3*c))) k*Ring.inverse x)
  let f (x : Residues u) : ℂ := cubicSymbol u (residueRepresentative u x)*
    residueFourierChar u hu0 (Ideal.Quotient.mk (modulus u) h*x+
      (Ideal.Quotient.mk (modulus u) k*
        (Ring.inverse (Ideal.Quotient.mk (modulus u) (3*c)))^2)*Ring.inverse x)
  let g (y : Residues (3*c)) : ℂ := cubicThetaEisensteinWeight c (residueRepresentative (3*c) y)*
    residueFourierChar (3*c) h3c (Ideal.Quotient.mk (modulus (3*c)) h*y+
      (Ideal.Quotient.mk (modulus (3*c)) k*
        (Ring.inverse (Ideal.Quotient.mk (modulus (3*c)) u))^2)*Ring.inverse y)
  let C : ℂ := cubicSymbol u (3*c)*cubicSymbol u c
  have hF (v : Residues u × Residues (3*c)) : F (e v)=C*(f v.1*g v.2) := by
    have hr : Ideal.Quotient.mk (modulus (u*(3*c)))
        (residueRepresentative (u*(3*c)) (e v))=
      Ideal.Quotient.mk (modulus (u*(3*c)))
        ((3*c)*residueRepresentative u v.1+u*residueRepresentative (3*c) v.2) :=
      residueRepresentative_spec _ _
    have hw := cubicThetaEisensteinWeight_congr_of_eq
      (dvd_mul_of_dvd_right hc u) hq hr
    dsimp only [F,f,g,C]
    rw [hw,cubicThetaEisensteinWeight_mix hu hc hcu]
    by_cases hx : IsUnit v.1
    · by_cases hy : IsUnit v.2
      · change _*residueFourierChar (u*(3*c)) (mul_ne_zero hu0 h3c)
          (Ideal.Quotient.mk (modulus (u*(3*c))) h*residueMix u (3*c) v+
            Ideal.Quotient.mk (modulus (u*(3*c))) k*Ring.inverse (residueMix u (3*c) v))=_
        rw [cubicThetaKloostermanPhase_mix hu0 h3c huc h k v.1 v.2 hx hy]
        ring
      · have hz := cubicThetaEisensteinResidueWeight_nonunit c v.2 hy
        change cubicThetaEisensteinWeight c (residueRepresentative (3*c) v.2)=0 at hz
        rw [hz]
        ring
    · rw [cubicThetaSymbol_nonunit_zero hu v.1 hx]
      ring
  rw [cubicThetaKloostermanSum_finite_of_eq h k (dvd_mul_of_dvd_right hc u)
    (mul_ne_zero hu0 hc0) (mul_ne_zero hu0 h3c) hq]
  change (∑' x,F x)=C*(∑' x,f x)*(∑' y,g y)
  rw [←e.tsum_eq]
  simp_rw [hF]
  rw [tsum_fintype,Fintype.sum_prod_type,tsum_fintype,tsum_fintype]
  calc
    _ = ∑ x : Residues u,(C*f x)*(∑ y : Residues (3*c),g y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (∑ x : Residues u,C*f x)*(∑ y : Residues (3*c),g y) := (Finset.sum_mul ..).symm
    _ = _ := by congr 1; rw [Finset.mul_sum]

end CubicFirstMoment

end

end OAI
