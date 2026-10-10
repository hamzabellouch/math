import OAI.Algebra.AffineCancellation.PositiveInvariant
import OAI.Algebra.AffineCancellation.FractionDerivation
import OAI.Algebra.AffineCancellation.DifferentialSlice

namespace OAI

noncomputable section

namespace ComplexCancellation.RationalSlice
open DifferentialSlice FractionDerivation
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [Algebra k R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K]

omit [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K] [CharZero k] in
lemma last_nonzero (D : Derivation k R R) {r : R} (hr : r ≠ 0)
    (h : ∃ m : ℕ, (D : R → R)^[m] r = 0) :
    ∃ n : ℕ, (D : R → R)^[n] r ≠ 0 ∧ D ((D : R → R)^[n] r) = 0 := by
  obtain ⟨m, hm⟩ := h
  induction m generalizing r with
  | zero => exact (hr hm).elim
  | succ m ih =>
    by_cases hdr : D r = 0
    · exact ⟨0, hr, hdr⟩
    · rw [Function.iterate_succ_apply] at hm
      obtain ⟨n, hn, hdn⟩ := ih hdr hm
      exact ⟨n+1, by simpa only [Function.iterate_succ_apply] using hn,
        by simpa only [Function.iterate_succ_apply] using hdn⟩

omit [CharZero k] [CharZero K] in
lemma exists_slice (D : Derivation k R R) (hD : LND.LocallyNilpotent D) (hne : D ≠ 0) :
    ∃ t : K, extend D t = 1 := by
  obtain ⟨r, hr⟩ : ∃ r : R, D r ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    ext r
    exact h r
  obtain ⟨n, hn, hdn⟩ := last_nonzero D hr (hD (D r))
  let s := (D : R → R)^[n] r
  have hs : D s ≠ 0 := by simpa only [s, ← Function.iterate_succ_apply',
    Function.iterate_succ_apply] using hn
  have hss : D (D s) = 0 := by simpa only [s, ← Function.iterate_succ_apply',
    Function.iterate_succ_apply] using hdn
  refine ⟨algebraMap R K s / algebraMap R K (D s), ?_⟩
  have hs' : algebraMap R K (D s) ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hs
  rw [Derivation.leibniz_div]
  simp only [extend_algebraMap, hss, map_zero, smul_eq_mul]
  field_simp
  ring

omit [CharZero k] [CharZero K] in
lemma iterate_constant_mul (D : Derivation k K K) {c : K} (hc : D c = 0) (r : K) (n : ℕ) :
    (D : K → K)^[n] (c * r) = c * (D : K → K)^[n] r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hc,
      smul_zero, add_zero, smul_eq_mul, Function.iterate_succ_apply']

omit [CharZero k] [CharZero K] in
lemma constant_fraction (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
    {c : K} (hc : extend D c = 0) :
    ∃ a b : R, D a = 0 ∧ D b = 0 ∧ b ≠ 0 ∧ algebraMap R K a / algebraMap R K b = c := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, hn, hdn⟩ := last_nonzero D hb0 (hD b)
  have hbK : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb0
  have hz : c * algebraMap R K b = algebraMap R K a := by rw [← hab]; exact div_mul_cancel₀ _ hbK
  have he := congrArg (fun z : K => (extend D : K → K)^[n] z) hz
  rw [iterate_constant_mul _ hc, iterate_algebraMap, iterate_algebraMap] at he
  refine ⟨(D : R → R)^[n] a, (D : R → R)^[n] b, ?_, hdn, hn, ?_⟩
  · apply IsFractionRing.injective R K
    rw [map_zero, ← extend_algebraMap, ← he, Derivation.leibniz, hc,
      extend_algebraMap, hdn, map_zero, smul_zero, smul_zero, add_zero]
  · rw [← he, mul_div_cancel_right₀ _ (by simpa using (IsFractionRing.injective R K).ne hn)]

omit [CharZero k] [IsDomain R] in
lemma image_is_polynomial (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
    {t : K} (ht : extend D t = 1) (r : R) :
    ∃ p : Polynomial (constants (extend (K := K) D)), Polynomial.aeval t p = algebraMap R K r := by
  apply nilpotent_is_polynomial _ ht
  obtain ⟨n, hn⟩ := hD r
  exact ⟨n, by rw [iterate_algebraMap, hn, map_zero]⟩

end ComplexCancellation.RationalSlice

end

end OAI
