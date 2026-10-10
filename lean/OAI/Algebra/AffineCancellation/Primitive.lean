import OAI.Algebra.AffineCancellation.FactorDerivation
import OAI.Algebra.AffineCancellation.Order

namespace OAI

noncomputable section

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
omit [CharZero k] [IsDomain R] in
lemma iterate_replica (D : Derivation k R R) (c : R) (hc : D c=0) (r : R) (n : ℕ) :
    ((c • D : Derivation k R R) : R → R)^[n] r=c^n*(D : R → R)^[n] r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Derivation.smul_apply,Derivation.leibniz,
      Derivation.leibniz_pow,hc]
    simp only [smul_eq_mul]
    rw [pow_succ,Function.iterate_succ_apply']
    ring

omit [CharZero k] [IsDomain R] in
lemma replica (D : Derivation k R R) (hD : LocallyNilpotent D) (c : R) (hc : D c=0) :
    LocallyNilpotent (c • D) := by
  intro r
  obtain ⟨n,hn⟩ := hD r
  exact ⟨n,by rw [iterate_replica D c hc,hn,mul_zero]⟩

/-- Remove all common powers of a regular parameter from an LND.
The termination certificate is the exact finite order of a single nonzero image. -/
lemma primitive_of_order (q : R) (hq : q ≠ 0) (w b s : R) (hs : ¬q ∣ s)
    (n : ℕ) (D : Derivation k R R) (hD : LocallyNilpotent D)
    (hDq : D q=0) (hDw : D w=0) (hb : D b=q^n*s) :
    ∃ E : Derivation k R R, LocallyNilpotent E ∧ E q=0 ∧ E w=0 ∧ ∃ r, ¬q ∣ E r := by
  induction n generalizing D with
  | zero =>
    refine ⟨D,hD,hDq,hDw,b,?_⟩
    rw [hb,pow_zero,one_mul]
    exact hs
  | succ n ih =>
    by_cases h : ∃ r, ¬q ∣ D r
    · exact ⟨D,hD,hDq,hDw,h⟩
    · push Not at h
      let f := AlgHom.id k R
      have hfac : ∀ r : R, ∃ s : R, D (f r)=q*f s := h
      let E := FactorDerivation.derivation f Function.injective_id D q hq hfac
      have he (r : R) : D r=q*E r := FactorDerivation.apply_spec f Function.injective_id D q hq hfac r
      have hE : LocallyNilpotent E := cancel_factor_locallyNilpotent f Function.injective_id D hD E hq he
      have hEq : E q=0 := (mul_eq_zero.mp (by rw [← he,hDq])).resolve_left hq
      have hEw : E w=0 := (mul_eq_zero.mp (by rw [← he,hDw])).resolve_left hq
      apply ih E hE hEq hEw
      apply mul_left_cancel₀ hq
      rw [← he,hb,pow_succ]
      ring
end ComplexCancellation.LND

end

end OAI
