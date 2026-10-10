import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKloostermanShift

namespace OAI

/-! Exact stationary-phase restriction in the finite prime-power
Kloosterman sum, obtained by averaging the square-zero shifts. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma finite_shift_stationary {R S : Type*} [AddCommGroup R] [Fintype R]
    [CommRing S] [Fintype S] (ψ : AddChar S ℂ) (hψ : ψ.IsPrimitive)
    (F : R → ℂ) (D : R → S) (t : S → R)
    (hF : ∀ b x,F (x+t b)=F x*ψ (b*D x)) :
    (∑ x : R,F x)=∑ x : R,if D x=0 then F x else 0 := by
  classical
  have hc : (Fintype.card S:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hc
  calc
    _ = ∑ b : S,∑ x : R,F (x+t b) := by
      have he (b : S) : (∑ x : R,F (x+t b))=∑ x : R,F x :=
        Equiv.sum_comp (Equiv.addRight (t b)) F
      simp_rw [he]
      simp
    _ = ∑ x : R,F x*(∑ b : S,ψ (b*D x)) := by
      simp_rw [hF]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      exact (Finset.mul_sum ..).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.sum_mulShift (D x) hψ]
      split_ifs <;> simp [mul_comm]

theorem cubicThetaPrimeKloosterman_stationary {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein) :
    cubicThetaSymbolKloosterman (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+2))) h)
      (Ideal.Quotient.mk (modulus (p^(n+2))) k)=
      ∑' x : Residues (p^(n+2)),if cubicThetaPrimeKloostermanDerivative p n h k x=0 then
        cubicSymbol (p^(n+2)) (residueRepresentative (p^(n+2)) x)*
          residueFourierChar (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
            (Ideal.Quotient.mk (modulus (p^(n+2))) h*x+
              Ideal.Quotient.mk (modulus (p^(n+2))) k*Ring.inverse x) else 0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Finite (Residues (p^(n+2))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues (p^(n+2))) := Fintype.ofFinite _
  have hprim : primary (p^(n+2)) := by
    rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
  let F : Residues (p^(n+2)) → ℂ := fun x =>
    cubicSymbol (p^(n+2)) (residueRepresentative (p^(n+2)) x)*
      residueFourierChar (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(n+2))) h*x+
          Ideal.Quotient.mk (modulus (p^(n+2))) k*Ring.inverse x)
  have hF (b : Residues p) (x : Residues (p^(n+2))) :
      F (x+cubicThetaPrimeKloostermanShift p n b)=
        F x*residueFourierChar p hp.2.ne_zero (b*cubicThetaPrimeKloostermanDerivative p n h k x) := by
    dsimp only [F]
    rw [cubicThetaPrimeKloostermanWeight_shift hp]
    by_cases hx : IsUnit x
    · rw [cubicThetaPrimeKloostermanPhase_shift hp n h k b x hx]
      ring
    · rw [cubicThetaSymbol_nonunit_zero hprim x hx,zero_mul,zero_mul,zero_mul]
  have he := finite_shift_stationary (residueFourierChar p hp.2.ne_zero)
    (residueFourierChar_isPrimitive p hp.2.ne_zero) F
    (cubicThetaPrimeKloostermanDerivative p n h k) (cubicThetaPrimeKloostermanShift p n) hF
  simpa only [cubicThetaSymbolKloosterman,tsum_fintype,F] using he

lemma cubicThetaPrimeKloostermanDerivative_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k)
    (x : Residues (p^(n+2))) (hx : IsUnit x) :
    cubicThetaPrimeKloostermanDerivative p n h k x≠0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  have hh0 : Ideal.Quotient.mk (modulus p) h=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hh)
  have hku : IsUnit (Ideal.Quotient.mk (modulus p) k) :=
    residue_isUnit_of_isCoprime (hp.2.coprime_iff_not_dvd.mpr hk)
  have hxu : IsUnit (residueReduction (dvd_pow_self p (by omega : n+2≠0)) x) :=
    hx.map (residueReduction (dvd_pow_self p (by omega : n+2≠0))).toMonoidHom
  unfold cubicThetaPrimeKloostermanDerivative
  rw [hh0,zero_sub]
  exact neg_ne_zero.mpr (hku.mul (hxu.ringInverse.pow 2)).ne_zero

theorem cubicThetaPrimeKloosterman_mismatch_zero {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h k : Eisenstein) (hh : p∣h) (hk : ¬p∣k) :
    cubicThetaSymbolKloosterman (p^(n+2)) (pow_ne_zero _ hp.2.ne_zero)
      (Ideal.Quotient.mk (modulus (p^(n+2))) h)
      (Ideal.Quotient.mk (modulus (p^(n+2))) k)=0 := by
  rw [cubicThetaPrimeKloosterman_stationary hp]
  trans (∑' _x : Residues (p^(n+2)),(0:ℂ))
  · apply tsum_congr
    intro x
    by_cases hx : IsUnit x
    · rw [ite_eq_right (cubicThetaPrimeKloostermanDerivative_ne_zero hp n h k hh hk x hx)]
    · have hprim : primary (p^(n+2)) := by
        rw [primary_iff_residue_one,map_pow,(primary_iff_residue_one p).mp hp.1,one_pow]
      rw [cubicThetaSymbol_nonunit_zero hprim x hx,zero_mul]
      split_ifs <;> rfl
  · exact tsum_zero

end CubicFirstMoment

end

end OAI
