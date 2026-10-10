import Mathlib.Algebra.MonoidAlgebra.Basic

namespace OAI

universe uR uG uH

/-!
# Division by regular coefficient scalars in an additive monoid algebra

A finite group algebra usually has zero divisors. A nonzero scalar from a
domain nevertheless acts injectively, as is seen separately at each coefficient.
This is the cancellation needed when the projected norm equation is divided by
one power of the residue characteristic.
-/

noncomputable section

namespace CirculantHadamard

section DivisionExists

variable {R : Type uR} {G : Type uG} [CommRing R] [AddMonoid G] [finiteG : Finite G]

/-- Coefficientwise divisibility produces an actual element of the finite
group algebra whose scalar multiple is the original element. -/
theorem scalar_division_exists (p : R) (F : AddMonoidAlgebra R G)
    (hF : ∀ g, p ∣ F.coeff g) :
    ∃ F' : AddMonoidAlgebra R G, F = AddMonoidAlgebra.single (0 : G) p * F' := by
  classical
  let d : G → R := fun g => Classical.choose (hF g)
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm d), ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  exact Classical.choose_spec (hF g)

omit finiteG in
/-- Multiplication by a scalar makes every coefficient divisible by that scalar. -/
theorem scalar_division_coefficients [Finite G] (p : R) (F : AddMonoidAlgebra R G) :
    ∀ g, p ∣ (AddMonoidAlgebra.single (0 : G) p * F).coeff g := by
  intro g
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  exact dvd_mul_right p (F.coeff g)

theorem scalar_division_iff (p : R) (F : AddMonoidAlgebra R G) :
    (∀ g, p ∣ F.coeff g) ↔
      ∃ F' : AddMonoidAlgebra R G, F = AddMonoidAlgebra.single (0 : G) p * F' := by
  constructor
  · exact scalar_division_exists p F
  · rintro ⟨F', rfl⟩
    exact scalar_division_coefficients p F'

end DivisionExists

section Cancellation

variable {R : Type uR} {G : Type uG} [CommRing R] [IsDomain R] [AddMonoid G]

/-- A scalar is cancellable because its action at each coefficient is
injective. No domain structure is asserted for the group algebra. -/
theorem scalar_mul_left_cancel (p : R) (hp : p ≠ 0)
    {F K : AddMonoidAlgebra R G}
    (h : AddMonoidAlgebra.single (0 : G) p * F =
      AddMonoidAlgebra.single (0 : G) p * K) : F = K := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  apply mul_left_cancel₀ hp
  simpa only [AddMonoidAlgebra.coeff_single_zero_mul] using
    congrArg (fun H : AddMonoidAlgebra R G => H.coeff g) h

theorem scalar_mul_left_injective (p : R) (hp : p ≠ 0) :
    Function.Injective
      (fun F : AddMonoidAlgebra R G => AddMonoidAlgebra.single (0 : G) p * F) :=
  fun _ _ h => scalar_mul_left_cancel p hp h

/-- The element obtained by coefficientwise division is unique. -/
theorem scalar_division_unique (p : R) (hp : p ≠ 0)
    {F F₁ F₂ : AddMonoidAlgebra R G}
    (h₁ : F = AddMonoidAlgebra.single (0 : G) p * F₁)
    (h₂ : F = AddMonoidAlgebra.single (0 : G) p * F₂) : F₁ = F₂ :=
  scalar_mul_left_cancel p hp (h₁.symm.trans h₂)

/-- Cancelling one regular scalar lowers the exponent of the norm equation
by exactly one. This is valid although the group algebra has zero divisors. -/
theorem scalar_mul_norm_division (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G)
    (h : (AddMonoidAlgebra.single (0 : G) p * F) * K =
      AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) :
    F * K = AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
  apply scalar_mul_left_cancel p hp
  calc
    AddMonoidAlgebra.single (0 : G) p * (F * K) =
        (AddMonoidAlgebra.single (0 : G) p * F) * K := (mul_assoc _ _ _).symm
    _ = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b) := h
    _ = AddMonoidAlgebra.single (0 : G) p *
        AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
      rw [pow_succ', mul_assoc]

end Cancellation

section Quotient

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R] [IsDomain R]
  [AddMonoid G] [AddMonoid H]

/-- Project the norm equation along a genuine ring homomorphism and then
divide the chosen projected factor by one coefficient scalar. -/
theorem quotient_scalar_norm_division
    (q : AddMonoidAlgebra R G →+* AddMonoidAlgebra R H)
    (hscalar : ∀ r : R, q (AddMonoidAlgebra.single (0 : G) r) =
      AddMonoidAlgebra.single (0 : H) r)
    (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G) (F' : AddMonoidAlgebra R H)
    (hFK : F * K = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b))
    (hF : q F = AddMonoidAlgebra.single (0 : H) p * F') :
    F' * q K = AddMonoidAlgebra.single (0 : H) (p ^ e * b) := by
  apply scalar_mul_norm_division p hp e b F' (q K)
  calc
    (AddMonoidAlgebra.single (0 : H) p * F') * q K = q F * q K := by rw [hF]
    _ = q (F * K) := (q.map_mul F K).symm
    _ = q (AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) := congrArg q hFK
    _ = AddMonoidAlgebra.single (0 : H) (p ^ (e + 1) * b) := hscalar _

end Quotient

end CirculantHadamard

end

end OAI
