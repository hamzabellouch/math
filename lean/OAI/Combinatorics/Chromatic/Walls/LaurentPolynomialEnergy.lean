import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section

def qLaurent : Polynomial ℕ →+* LaurentSeries ℚ:=
  Polynomial.eval₂RingHom (Nat.castRingHom _) (HahnSeries.single (-2) 1)
lemma qLaurent_monomial (k a:ℕ) : qLaurent (Polynomial.monomial k a)=HahnSeries.single (-2*(k:ℤ)) (a:ℚ) := by
  change Polynomial.eval₂ (Nat.castRingHom _) (HahnSeries.single (-2) 1) (Polynomial.monomial k a)=_
  rw [Polynomial.eval₂_monomial]
  change (a:LaurentSeries ℚ)*HahnSeries.single (-2) 1 ^ k=_
  rw [←HahnSeries.single_zero_natCast,HahnSeries.single_pow,HahnSeries.single_mul_single]
  simp [mul_comm]

def centered (M:ℕ) (p:Polynomial ℕ):LaurentSeries ℚ:=HahnSeries.single (M:ℤ) 1*qLaurent p
lemma centered_zero (M:ℕ) : centered M 0=0:=by simp [centered]
lemma centered_add (M:ℕ) (p q:Polynomial ℕ) : centered M (p+q)=centered M p+centered M q:=by
  simp [centered,mul_add]
lemma centered_sum {A:Type*} [Fintype A] (M:ℕ) (p:A → Polynomial ℕ) :
    centered M (∑a,p a)=∑a,centered M (p a):=by simp [centered,Finset.mul_sum]
lemma centered_mul (M:ℕ) (p q:Polynomial ℕ) : centered M (p*q)=centered M p*qLaurent q:=by
  simp [centered,mul_assoc]
lemma centered_monomial (M k a:ℕ) :
    centered M (Polynomial.monomial k a)=HahnSeries.single ((M:ℤ)-2*(k:ℤ)) (a:ℚ) := by
  rw [centered,qLaurent_monomial,HahnSeries.single_mul_single,one_mul]
  congr 1
lemma centered_coeff (M:ℕ) (p:Polynomial ℕ) (k:ℕ) :
    (centered M p).coeff ((M:ℤ)-2*(k:ℤ))=(p.coeff k:ℚ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>rw [centered_add,HahnSeries.coeff_add,Polynomial.coeff_add,Nat.cast_add,hp,hq]
  | monomial e a=>
    rw [centered_monomial,HahnSeries.coeff_single,Polynomial.coeff_monomial]
    have he:((M:ℤ)-2*(k:ℤ)=(M:ℤ)-2*(e:ℤ)) ↔ e=k:=by omega
    simp only [he]
    split_ifs <;> simp
lemma centered_injective (M:ℕ) : Function.Injective (centered M) := by
  intro p q h
  ext k
  have H:=congrArg (fun w:LaurentSeries ℚ=>w.coeff ((M:ℤ)-2*(k:ℤ))) h
  rw [centered_coeff,centered_coeff] at H
  exact_mod_cast H
lemma centered_X_pow (M k:ℕ) :
    centered M (Polynomial.X^k)=(↑(LaurentRay.vUnit^(2*(k:ℤ)-(M:ℤ))):LaurentSeries ℚ) := by
  rw [←Polynomial.monomial_one_right_eq_X_pow,centered_monomial,LaurentRay.vUnit_zpow]
  congr 1
  ring_nf

lemma map_elementary_coeff {A B:Type*} [Fintype A] [Fintype B]
    (μ:A →₀ ℕ) (a:B →₀ ℕ) :
    qLaurent ((∏i:A,MvPolynomial.esymm B (Polynomial ℕ) (μ i)).coeff a)=
      (∏i:A,MvPolynomial.esymm B (LaurentSeries ℚ) (μ i)).coeff a := by
  rw [←MvPolynomial.coeff_map]
  simp only [map_prod,MvPolynomial.map_esymm]
end
end ElementaryPositivity.LaurentPositive

end

end OAI
