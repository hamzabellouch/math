import OAI.Algebra.AffineCancellation.Kernel

namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

omit [CharZero k] [IsDomain R] in
lemma orbit_ne_zero (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R} (hr : r ≠ 0) :
    orbit D hD r ≠ 0 := by
  intro h
  apply hr
  simpa using congrArg (fun f : R[X] => f.coeff 0) h

def order (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) : ℕ :=
  (orbit D hD r).natDegree

lemma order_mul (D : Derivation k R R) (hD : LocallyNilpotent D) {r s : R}
    (hr : r ≠ 0) (hs : s ≠ 0) : order D hD (r*s) = order D hD r + order D hD s := by
  exact (congrArg natDegree (orbit_mul D hD r s)).trans
    (natDegree_mul (orbit_ne_zero D hD hr) (orbit_ne_zero D hD hs))

omit [CharZero k] [IsDomain R] in
lemma order_zero_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    order D hD r = 0 ↔ D r = 0 := by
  rw [← orbit_constant_iff D hD r]
  constructor
  · intro hr
    simpa using eq_C_of_natDegree_eq_zero hr
  · intro h
    simp only [order, h, natDegree_C]

lemma order_derivative (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R}
    (hr : D r ≠ 0) : order D hD (D r) + 1 = order D hD r := by
  let : CharZero R := Algebra.charZero_of_charZero k R
  have hpos : 0 < order D hD r := Nat.pos_of_ne_zero (mt (order_zero_iff D hD r).mp hr)
  change (orbit D hD (D r)).natDegree+1 = _
  rw [← derivative_orbit, natDegree_derivative]
  change order D hD r - 1 + 1 = order D hD r
  omega

/-- Dividing a locally nilpotent derivation by a nonzero common factor still
produces a locally nilpotent derivation, even if the factor is not invariant. -/
lemma cancel_factor_locallyNilpotent {S : Type*} [CommRing S] [Algebra k S]
    (f : S →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k R R) (hD : LocallyNilpotent D)
    (E : Derivation k S S) {c : R} (hc : c ≠ 0)
    (h : ∀ r : S, D (f r) = c * f (E r)) : LocallyNilpotent E := by
  intro r
  induction hn : order D hD (f r) using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases her : E r = 0
    · exact ⟨1, her⟩
    · have hfer : f (E r) ≠ 0 := by simpa only [map_zero] using hf.ne her
      have hdr : D (f r) ≠ 0 := by rw [h]; exact mul_ne_zero hc hfer
      have ho := order_derivative D hD hdr
      rw [h, order_mul D hD hc hfer, hn] at ho
      obtain ⟨m, hm⟩ := ih (order D hD (f (E r))) (by omega) (E r) rfl
      exact ⟨m+1, by simpa only [Function.iterate_succ_apply] using hm⟩

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [CommRing S] [Algebra k S] [Algebra k R]
lemma cancel_factor_square_zero
    (f : S →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k R R) (hD : LocallyNilpotent D)
    (E : Derivation k S S) {c : R} (hc : c ≠ 0)
    (h : ∀ r : S, D (f r)=c*f (E r)) (v : S)
    (ho : order D hD (f v) ≤ 2*order D hD c) : E (E v)=0 := by
  by_contra hEE
  have hE : E v ≠ 0 := by intro he; apply hEE; rw [he,map_zero]
  have hn (r : S) (hr : E r ≠ 0) :
      order D hD c + order D hD (f (E r)) + 1 = order D hD (f r) := by
    have hfr : f (E r) ≠ 0 := by simpa only [map_zero] using hf.ne hr
    have hdr : D (f r) ≠ 0 := by rw [h]; exact mul_ne_zero hc hfr
    have he := order_derivative D hD hdr
    rwa [h,order_mul D hD hc hfr] at he
  have h₁ := hn v hE
  have h₂ := hn (E v) hEE
  omega
end ComplexCancellation.LND

end

end OAI
