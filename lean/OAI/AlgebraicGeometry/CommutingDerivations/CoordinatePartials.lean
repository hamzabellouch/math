import OAI.AlgebraicGeometry.CommutingDerivations.DerivationOperations
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace OAI

/-! The actual polynomial coordinate partials: commuting, locally nilpotent,
linearly independent over the polynomial ring, and with exact constant common
kernel in characteristic zero. No localization equivalence is assumed here. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {B σ : Type*} [CommRing B]

theorem coordinate_partials_commute (i j : σ) (p : MvPolynomial σ B) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp [coeff_pderiv, Finsupp.add_apply, hij, Ne.symm hij,
    add_comm, add_left_comm, mul_comm, mul_left_comm]

/-- Vanishing of all coefficients at exponent at least n implies annihilation
by the nth partial iterate. This works over every commutative ring. -/
theorem coordinate_partial_iterate_eq_zero (i : σ) (n : ℕ) (p : MvPolynomial σ B)
    (hp : ∀ m : σ →₀ ℕ, n ≤ m i → p.coeff m = 0) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[n] p = 0 := by
  classical
  induction n generalizing p with
  | zero =>
      apply MvPolynomial.ext
      intro m
      simpa using hp m (Nat.zero_le _)
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      apply ih
      intro m hm
      rw [coeff_pderiv]
      have hz : p.coeff (m + Finsupp.single i 1) = 0 := by
        apply hp
        simpa using Nat.succ_le_succ hm
      rw [hz, zero_mul]

/-- An explicit pointwise bound: one more than the largest exponent of i
among the finitely many supported monomials. -/
theorem coordinate_partial_nilpotence_bound (i : σ) (p : MvPolynomial σ B) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[
      p.support.sup (fun m => m i) + 1] p = 0 := by
  classical
  apply coordinate_partial_iterate_eq_zero
  intro m hm
  by_contra hc
  have hmem : m ∈ p.support := mem_support_iff.mpr hc
  have hle : m i ≤ p.support.sup (fun a => a i) :=
    Finset.le_sup (f := fun a : σ →₀ ℕ => a i) hmem
  exact (Nat.not_succ_le_self _) (hm.trans hle)

theorem coordinate_partial_locallyNilpotent (i : σ) :
    LocallyNilpotent (pderiv i : Derivation B (MvPolynomial σ B) (MvPolynomial σ B)) := by
  intro p
  exact ⟨p.support.sup (fun m => m i) + 1, coordinate_partial_nilpotence_bound i p⟩

/-- Exact coefficient consequence of the common-kernel condition. -/
theorem coefficient_eq_zero_of_all_partials_zero [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) (hp : ∀ i, pderiv i p = 0)
    (m : σ →₀ ℕ) (hm : m ≠ 0) : p.coeff m = 0 := by
  classical
  have hex : ∃ i, m i ≠ 0 := by
    by_contra hh
    apply hm
    ext i
    change m i = 0
    by_contra hi
    exact hh ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have he := congrArg (fun polynomial : MvPolynomial σ B =>
    polynomial.coeff (m - Finsupp.single i 1)) (hp i)
  rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi,
    AddMonoidAlgebra.coeff_zero] at he
  have hfactor : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : B) + 1 ≠ 0 := by
    rw [← Nat.cast_succ]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  exact (mul_eq_zero.mp he).resolve_right hfactor

/-- The common kernel is literally the coefficient ring, with witness equal
to the constant coefficient. In particular this applies to Laurent coefficients
over C, once that coefficient algebra's domain and characteristic are installed. -/
theorem coordinate_partials_common_kernel [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) :
    (∀ i, pderiv i p = 0) ↔ ∃ b : B, p = C b := by
  classical
  constructor
  · intro hp
    refine ⟨p.coeff 0, ?_⟩
    ext m
    by_cases hm : m = 0
    · subst m
      simp
    · rw [coefficient_eq_zero_of_all_partials_zero p hp m hm, coeff_C_of_ne_zero hm]
  · rintro ⟨b, rfl⟩ i
    exact pderiv_C

theorem coordinate_partials_linearIndependent [Fintype σ] :
    LinearIndependent (MvPolynomial σ B)
      (fun i : σ => (pderiv i : Derivation B (MvPolynomial σ B) (MvPolynomial σ B))) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  let ev : Derivation B (MvPolynomial σ B) (MvPolynomial σ B) →+ MvPolynomial σ B :=
    { toFun := fun D => D (X j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev ha
  rw [map_sum, map_zero] at he
  simpa [ev, Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply] using he

end AbhyankarSathaye.CommutingDerivations

end

end OAI
