import Mathlib.RingTheory.ZMod.UnitsCyclic
import OAI.NumberTheory.Ostmann.Arithmetic.CRTResidueAverage

namespace OAI

/-! # Square congruences in the frequency support -/

namespace Ostmann

open scoped BigOperators Classical

def squareFiberEquivOne {G : Type*} [CommGroup G] (r : G) :
    {x : G // x ^ 2 = r ^ 2} ≃ {x : G // x ^ 2 = 1} where
  toFun x := ⟨x / r, by rw [div_pow, x.property, div_self']⟩
  invFun x := ⟨x * r, by rw [mul_pow, x.property, one_mul]⟩
  left_inv x := by ext; exact div_mul_cancel x.val r
  right_inv x := by ext; exact mul_div_cancel_right x.val r

theorem cyclic_square_fiber_card_le {G : Type*} [CommGroup G] [Fintype G]
    [IsCyclic G] (a : G) : Nat.card {x : G // x ^ 2 = a} ≤ 2 := by
  classical
  rw [Nat.card_eq_fintype_card]
  by_cases h : ∃ r : G, r ^ 2 = a
  · obtain ⟨r, rfl⟩ := h
    rw [Fintype.card_congr (squareFiberEquivOne r)]
    simpa only [Fintype.card_subtype] using (IsCyclic.card_pow_eq_one_le (α := G) (by decide : 0 < 2))
  · have hi : IsEmpty {x : G // x ^ 2 = a} := ⟨fun x => h ⟨x, x.property⟩⟩
    rw [Fintype.card_of_isEmpty]
    omega

/-- The odd-prime-power part of the manuscript's square-root bound follows
from Mathlib's proved cyclicity of the unit group. -/
theorem odd_prime_power_square_fiber_card_le (p n : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (a : (ZMod (p ^ n))ˣ) :
    Nat.card {x : (ZMod (p ^ n))ˣ // x ^ 2 = a} ≤ 2 := by
  let _ : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let _ : IsCyclic (ZMod (p ^ n))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 n
  exact cyclic_square_fiber_card_le a

noncomputable def crtSquareFiberEquiv {I : Type*} [Fintype I]
    (q : I → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (a : (ZMod (∏ i, q i))ˣ) :
    {x : (ZMod (∏ i, q i))ˣ // x ^ 2 = a} ≃
      ∀ i, {x : (ZMod (q i))ˣ // x ^ 2 = crtUnitEquiv q hc a i} :=
  ((crtUnitEquiv q hc).toEquiv.subtypeEquiv (by
    intro x
    constructor
    · intro hx i
      simpa only [map_pow, Pi.pow_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using
        congrArg (fun y => crtUnitEquiv q hc y i) hx
    · intro hx
      apply (crtUnitEquiv q hc).injective
      funext i
      simpa only [map_pow, Pi.pow_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
        using hx i)).trans Equiv.subtypePiEquivPi

theorem crt_square_fiber_card {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (a : (ZMod (∏ i, q i))ˣ) :
    Nat.card {x : (ZMod (∏ i, q i))ˣ // x ^ 2 = a} =
      ∏ i, Nat.card {x : (ZMod (q i))ˣ // x ^ 2 = crtUnitEquiv q hc a i} := by
  rw [Nat.card_congr (crtSquareFiberEquiv q hc a)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi]

/-- Exact CRT factorization gives the full odd-prime-power square bound. -/
theorem odd_prime_powers_square_fiber_card_le {I : Type*} [Fintype I]
    (p n : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i ^ n i)]
    [NeZero (∏ i, p i ^ n i)]
    (hp2 : ∀ i, p i ≠ 2)
    (hc : Pairwise (fun i j => (p i ^ n i).Coprime (p j ^ n j)))
    (a : (ZMod (∏ i, p i ^ n i))ˣ) :
    Nat.card {x : (ZMod (∏ i, p i ^ n i))ˣ // x ^ 2 = a} ≤ 2 ^ Fintype.card I := by
  rw [crt_square_fiber_card (fun i => p i ^ n i) hc a]
  calc
    _ ≤ ∏ _i : I, 2 := Finset.prod_le_prod fun i _ =>
      odd_prime_power_square_fiber_card_le (p i) (n i) (hp2 i) _
    _ = _ := by simp

end Ostmann

end OAI
