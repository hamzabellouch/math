import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterReduction

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

private theorem card_mul_group_fibre {A B : Type*} [Group A] [Fintype A]
    [Group B] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (b : B) :
    Fintype.card B * ((Finset.univ : Finset A).filter fun x => f x = b).card =
      Fintype.card A := by
  calc
    _ = ∑ _y : B, ((Finset.univ : Finset A).filter fun x => f x = b).card := by simp
    _ = ∑ y : B, ((Finset.univ : Finset A).filter fun x => f x = y).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf y)
    _ = _ := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp

theorem unit_reduction_fibre_card (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (v : (ZMod (p^s))ˣ) :
    ((Finset.univ : Finset (ZMod (p*p^s))ˣ).filter fun u =>
      ZMod.unitsMap (dvd_mul_left (p^s) p) u = v).card = p := by
  let f : (ZMod (p*p^s))ˣ →* (ZMod (p^s))ˣ := ZMod.unitsMap (dvd_mul_left (p^s) p)
  have hf : Function.Surjective f := ZMod.unitsMap_surjective (dvd_mul_left (p^s) p)
  have hc := card_mul_group_fibre f hf v
  have htot : Fintype.card (ZMod (p*p^s))ˣ = Fintype.card (ZMod (p^s))ˣ * p := by
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, ← pow_succ',
      Nat.totient_prime_pow_succ (Fact.out : p.Prime),
      Nat.totient_prime_pow (Fact.out : p.Prime) hs]
    have he : p^s = p^(s-1)*p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he]
    ring
  rw [htot] at hc
  simpa only [f] using Nat.eq_of_mul_eq_mul_left
    (show 0 < Fintype.card (ZMod (p^s))ˣ from Fintype.card_pos) hc

theorem sum_comp_unit_reduction (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (f : (ZMod (p^s))ˣ → ℂ) :
    (∑ u : (ZMod (p*p^s))ˣ, f (ZMod.unitsMap (dvd_mul_left (p^s) p) u)) =
      (p : ℂ) * ∑ v : (ZMod (p^s))ˣ, f v := by
  rw [← Finset.sum_fiberwise' Finset.univ (ZMod.unitsMap (dvd_mul_left (p^s) p)) f]
  simp only [Finset.sum_const, unit_reduction_fibre_card p s hs, nsmul_eq_mul,
    ← Finset.mul_sum]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
