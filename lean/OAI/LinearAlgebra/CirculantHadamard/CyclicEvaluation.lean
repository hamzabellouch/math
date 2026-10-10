import OAI.LinearAlgebra.CirculantHadamard.CyclicRing

namespace OAI

universe uR uS uT uA

/-!
# Evaluation of the finite cyclic group ring

Evaluation is a ring homomorphism obtained from a coefficient homomorphism and
an actual character of the cyclic group.  Its compatibility with the group-ring
involution is proved from the coefficient and character identities.
-/

noncomputable section

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n : ℕ}

/-- Evaluation at a multiplicative character of the additive cyclic group. -/
def evaluate (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) : Elem R n →+* S :=
  AddMonoidAlgebra.liftNCRingHom φ χ (fun _ _ => Commute.all _ _)

@[simp] theorem evaluate_single (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (a : ZMod n) (r : R) :
    evaluate φ χ (AddMonoidAlgebra.single a r) = φ r * χ (Multiplicative.ofAdd a) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

@[simp] theorem evaluate_scalar (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (r : R) :
    evaluate φ χ (scalar n r) = φ r := by
  simp only [scalar, evaluate_single]
  change φ r * χ 1 = φ r
  simp

/-- The full finite sum, rather than a sum over an unspecified support. -/
theorem evaluate_apply [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (f : Elem R n) :
    evaluate φ χ f = ∑ a : ZMod n, φ (f.coeff a) * χ (Multiplicative.ofAdd a) := by
  change f.coeff.sum (fun a r => φ r * χ (Multiplicative.ofAdd a)) = _
  exact Finsupp.sum_fintype f.coeff _ (fun _ => by simp)

@[simp] theorem evaluate_ofCoeffs [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (c : ZMod n → R) :
    evaluate φ χ (ofCoeffs c) = ∑ a : ZMod n, φ (c a) * χ (Multiplicative.ofAdd a) :=
  evaluate_apply φ χ (ofCoeffs c)

/-- The trivial character recovers augmentation followed by the coefficient map. -/
theorem evaluate_trivial_eq_augmentation [NeZero n] (φ : R →+* S)
    (f : Elem R n) :
    evaluate φ (1 : Multiplicative (ZMod n) →* S) f = φ (augmentation n f) := by
  simp [evaluate_apply, augmentation_apply, map_sum]

/-- Evaluation commutes with a change of target coefficient ring. -/
theorem map_evaluate [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (ψ : S →+* T) (f : Elem R n) :
    ψ (evaluate φ χ f) = evaluate (ψ.comp φ) (ψ.toMonoidHom.comp χ) f := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact map_mul ψ (φ (f.coeff a)) (χ (Multiplicative.ofAdd a))

/-- Bundled naturality of character evaluation. -/
theorem map_evaluate_hom [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (ψ : S →+* T) :
    ψ.comp (evaluate φ χ) = evaluate (ψ.comp φ) (ψ.toMonoidHom.comp χ) := by
  apply RingHom.ext
  intro f
  exact map_evaluate φ χ ψ f

/-- A target endomorphism intertwines evaluation and the full group-ring star
when it intertwines the coefficient involution and character inversion. -/
theorem evaluate_ringStar_intertwining [StarRing R] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) (τ : S →+* S)
    (hφ : ∀ r, φ (star r) = τ (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = τ (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = τ (evaluate φ χ f) := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ ?_
  intro a
  simp only [ringStar_apply, Equiv.neg_apply, map_mul, hφ]
  rw [← hχ]
  simp only [neg_neg]

/-- Character evaluation carries the full group-ring involution to target star. -/
theorem evaluate_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = star (evaluate φ χ f) :=
  evaluate_ringStar_intertwining φ χ (starRingEnd S) hφ hχ f

/-- The group-ring norm product becomes the usual star norm product. -/
theorem evaluate_mul_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (f * ringStar f) = evaluate φ χ f * star (evaluate φ χ f) := by
  rw [map_mul, evaluate_ringStar φ χ hφ hχ]

/-- A proved scalar group-ring norm equation transfers to every compatible
character; the norm equation is not built into the evaluation definition. -/
theorem evaluate_norm_eq [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) (r : R) (hf : f * ringStar f = scalar n r) :
    evaluate φ χ f * star (evaluate φ χ f) = φ r := by
  rw [← evaluate_mul_ringStar φ χ hφ hχ, hf, evaluate_scalar]

/-- For integer coefficients, coefficient-star compatibility is automatic. -/
theorem evaluate_int_ringStar {A : Type uA} [CommRing A] [StarRing A] [NeZero n]
    (χ : Multiplicative (ZMod n) →* A)
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem ℤ n) :
    evaluate (Int.castRingHom A) χ (ringStar f) =
      star (evaluate (Int.castRingHom A) χ f) := by
  exact evaluate_ringStar (Int.castRingHom A) χ (fun r => by simp) hχ f

end CirculantHadamard.CyclicRing

end

end OAI
