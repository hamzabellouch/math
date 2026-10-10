import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteFourierParseval
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanFinite

namespace OAI

/-! Finite Fourier realization and exact Gram identity for the actual
Kloosterman weights, retaining their zero extension at common factors. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaFiniteKloosterman (c : Eisenstein) (hc0 : c≠0)
    (h k : Residues (3*c)) : ℂ :=
  ∑' x : Residues (3*c),cubicThetaEisensteinResidueWeight c x*
    residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) (h*x+k*Ring.inverse x)

lemma cubicThetaFiniteKloosterman_integer (h k : Eisenstein) {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) :
    cubicThetaFiniteKloosterman c hc0 (Ideal.Quotient.mk (modulus (3*c)) h)
      (Ideal.Quotient.mk (modulus (3*c)) k)=cubicThetaKloostermanSum h k c hc :=
  (cubicThetaKloostermanSum_finite h k hc hc0).symm

lemma cubicThetaFiniteKloosterman_fourier (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (h k : Residues (3*c)) :
    cubicThetaFiniteKloosterman c hc0 h k=
      cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0)
        (fun x => cubicThetaEisensteinResidueWeight c x*
          residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) (k*Ring.inverse x)) h := by
  simp only [cubicThetaFiniteKloosterman,tsum_fintype,cubicThetaFiniteFourier,
    AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem cubicThetaFiniteKloosterman_gram (c : Eisenstein) (hc0 : c≠0)
    (k l : Residues (3*c)) :
    (∑' h : Residues (3*c),cubicThetaFiniteKloosterman c hc0 h k*
      star (cubicThetaFiniteKloosterman c hc0 h l))=
      (9*norm c:ℂ)*∑' x : Residues (3*c),
        (cubicThetaEisensteinResidueWeight c x*star (cubicThetaEisensteinResidueWeight c x))*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) ((k-l)*Ring.inverse x) := by
  classical
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues (3*c)):ℂ)=(9*norm c:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (mul_ne_zero (by norm_num) hc0)]
    have h3 : norm (3:Eisenstein)=9 := by
      change Complex.normSq (3:ℂ)=9
      norm_num
    have hn : (normNat (3*c):ℝ)=9*norm c := by
      rw [normNat_cast,norm_mul_eq,h3]
    exact_mod_cast hn
  simp only [tsum_fintype,cubicThetaFiniteKloosterman_fourier]
  rw [cubicThetaFiniteFourier_parseval,hcard]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul,cubicThetaResidueFourier_star]
  have he : residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) (k*Ring.inverse x)*
      residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) (-(l*Ring.inverse x))=
      residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) ((k-l)*Ring.inverse x) := by
    rw [←AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = (cubicThetaEisensteinResidueWeight c x*star (cubicThetaEisensteinResidueWeight c x))*
        (residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) (k*Ring.inverse x)*
          residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc0) (-(l*Ring.inverse x))) := by ring
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
