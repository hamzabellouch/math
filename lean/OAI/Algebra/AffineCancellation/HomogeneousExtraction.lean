import OAI.Algebra.AffineCancellation.FactorDerivation
import OAI.Algebra.AffineCancellation.Order
import OAI.Algebra.AffineCancellation.Extraction

namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
include hv

omit [CharZero k] in
lemma euler_factor (H : Derivation k R R) (hH : H v=2*v)
    (D : Derivation k (T R v) (T R v))
    (hcomm : ∀ z, euler v H hH (D z)=D (euler v H hH z))
    (E : Derivation k R R) (c : T R v) (hc : c ≠ 0) (n : ℕ)
    (hcn : euler v H hH c=n • c)
    (hspec : ∀ r, D (coefficientHom (k := k) v r)=c*coefficientHom (k := k) v (E r)) :
    ∀ r, H (E r)-E (H r)=-(n • E r) := by
  let := isDomain R v hv
  intro r
  apply coefficientHom_injective (k := k) v
  apply mul_left_cancel₀ hc
  have he := hcomm (coefficientHom (k := k) v r)
  rw [hspec,euler_coefficient,hspec,Derivation.leibniz,euler_coefficient,hcn] at he
  simp only [map_sub,map_neg,smul_eq_mul,nsmul_eq_mul,map_mul,map_natCast] at he ⊢
  linear_combination he

lemma fixed_τ_of_fixed_v (D : Derivation k (T R v) (T R v))
    (hD : LND.LocallyNilpotent D) (h : D (coefficientHom (k := k) v v)=0) : D (τ R v)=0 := by
  let := isDomain R v hv
  have hnτ := τ_nonzero v
  have hnV := V_nonzero v hv
  apply (LND.kernel_factorially_closed D hD hnτ (mul_ne_zero hnτ hnV) _).1
  have he : τ R v*(τ R v*V R v)=coefficientHom (k := k) v v := by
    change τ R v*(τ R v*V R v)=algebraMap R (T R v) v
    simpa only [pow_two,mul_assoc] using equation R v
  rwa [he]

lemma coefficient_order (D : Derivation k (T R v) (T R v))
    (hD : LND.LocallyNilpotent D) (hV : D (V R v)=0) :
    LND.order D hD (coefficientHom (k := k) v v)=2*LND.order D hD (τ R v) := by
  let := isDomain R v hv
  have h₀ := (LND.order_zero_iff D hD (V R v)).mpr hV
  change LND.order D hD (algebraMap R (T R v) v)=_
  rw [← equation R v,pow_two,
    LND.order_mul D hD (mul_ne_zero (τ_nonzero v) (τ_nonzero v)) (V_nonzero v hv),
    LND.order_mul D hD (τ_nonzero v) (τ_nonzero v),h₀]
  omega

lemma order_monomial_fixed_V (D : Derivation k (T R v) (T R v))
    (hD : LND.LocallyNilpotent D) (hV : D (V R v)=0) (n : ℕ) :
    LND.order D hD (τ R v*V R v^n)=LND.order D hD (τ R v) := by
  let := isDomain R v hv
  rw [LND.order_mul D hD (τ_nonzero v) (pow_ne_zero _ (V_nonzero v hv))]
  have he : D (V R v^n)=0 := by simp [Derivation.leibniz_pow,hV]
  rw [(LND.order_zero_iff D hD _).mpr he,add_zero]

/-- Extraction of a coefficient derivation without assuming invariance of the coefficient ring. -/
theorem extract (H : Derivation k R R) (hH : H v=2*v)
    (D : Derivation k (T R v) (T R v)) (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0)
    (j : ℤ) (hshift : ∀ e r, r ∈ pieces R v e → D r ∈ pieces R v (e+j))
    (hcomm : ∀ z, euler v H hH (D z)=D (euler v H hH z))
    (hV : D (V R v)=0) :
    ∃ (E : Derivation k R R) (n : ℕ), E ≠ 0 ∧ LND.LocallyNilpotent E ∧
      (∀ r, H (E r)-E (H r)=-(n • E r)) ∧ E (E v)=0 := by
  let := isDomain R v hv
  let f := coefficientHom (k := k) v
  have hf : Function.Injective f := coefficientHom_injective v
  have hcoeff (r : R) : D (f r) ∈ pieces R v j := by
    simpa only [zero_add] using hshift 0 (f r) (coefficient_mem R v r)
  by_cases ht : D (τ R v)=0
  · obtain ⟨i,h,hpiece⟩ := piece_monomial R v j
    let c := τ R v^i*V R v^h
    have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (τ_nonzero v)) (pow_ne_zero _ (V_nonzero v hv))
    have hspec : ∀ r : R, ∃ s : R, D (f r)=c*f s := fun r => hpiece _ (hcoeff r)
    let E := FactorDerivation.derivation f hf D c hc hspec
    have he (r : R) : D (f r)=c*f (E r) := FactorDerivation.apply_spec f hf D c hc hspec r
    have hEv : E v=0 := by
      apply hf
      apply mul_left_cancel₀ hc
      rw [map_zero,mul_zero,← he]
      change D (algebraMap R (T R v) v)=0
      rw [← equation R v]
      simp [Derivation.leibniz,Derivation.leibniz_pow,ht,hV]
    refine ⟨E,2*h,?_,LND.cancel_factor_locallyNilpotent f hf D hD E hc he,?_,?_⟩
    · intro hE
      apply hDn
      apply derivation_zero_of_generators v D _ ht hV
      intro r
      rw [he,hE,Derivation.zero_apply,map_zero,mul_zero]
    · apply euler_factor v hv H hH D hcomm E c hc (2*h) _ he
      simpa only [nsmul_eq_mul] using euler_monomial v H hH i h
    · rw [hEv,map_zero]
  · have hnt : ¬τ R v ∣ D (τ R v) := fun he => ht (LND.fixed_of_dvd D hD he)
    obtain ⟨l,hl⟩ := degree_even_of_not_τ_dvd R v (hshift (-1) _ (τ_mem R v)) hnt
    have hj : j=2*(l:ℤ)+1 := by omega
    have hspec : ∀ r : R, ∃ s : R, D (f r)=(τ R v*V R v^(l+1))*f s := by
      intro r
      exact piece_odd R v l (hj ▸ hcoeff r)
    let c := τ R v*V R v^(l+1)
    have hc : c ≠ 0 := mul_ne_zero (τ_nonzero v) (pow_ne_zero _ (V_nonzero v hv))
    let E := FactorDerivation.derivation f hf D c hc hspec
    have he (r : R) : D (f r)=c*f (E r) := FactorDerivation.apply_spec f hf D c hc hspec r
    refine ⟨E,2*(l+1),?_,LND.cancel_factor_locallyNilpotent f hf D hD E hc he,?_,?_⟩
    · intro hE
      apply ht
      apply fixed_τ_of_fixed_v v hv D hD
      rw [he,hE,Derivation.zero_apply,map_zero,mul_zero]
    · apply euler_factor v hv H hH D hcomm E c hc (2*(l+1)) _ he
      simpa only [pow_one,nsmul_eq_mul] using euler_monomial v H hH 1 (l+1)
    · apply LND.cancel_factor_square_zero f hf D hD E hc he v
      rw [coefficient_order v hv D hD hV,order_monomial_fixed_V v hv D hD hV]
lemma fixed_V_of_positive_invariant
    (D : Derivation k (T R v) (T R v)) (hD : LND.LocallyNilpotent D)
    (w : T R v) (hw : w ≠ 0) (e : ℤ) (he : 0 < e)
    (hwg : w ∈ pieces R v e) (hDw : D w=0) : D (V R v)=0 := by
  let := isDomain R v hv
  obtain ⟨z,hz⟩ := V_dvd_of_positive R v he hwg
  have hzn : z ≠ 0 := by intro he; rw [he,mul_zero] at hz; exact hw hz
  apply (LND.kernel_factorially_closed D hD (V_nonzero v hv) hzn _).1
  rwa [← hz]
end ComplexCancellation.AffineModification

end

end OAI
