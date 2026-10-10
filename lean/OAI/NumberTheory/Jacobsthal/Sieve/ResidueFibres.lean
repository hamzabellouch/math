import Mathlib.GroupTheory.Index
import OAI.NumberTheory.Jacobsthal.Primes.PrimePowerStationarity

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

private theorem card_mul_fibre {A B : Type*} [AddGroup A] [Fintype A]
    [AddGroup B] [Fintype B] (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    Fintype.card B * ((Finset.univ : Finset A).filter fun x => f x = b).card =
      Fintype.card A := by
  calc
    _ = ∑ _y : B, ((Finset.univ : Finset A).filter fun x => f x = b).card := by simp
    _ = ∑ y : B, ((Finset.univ : Finset A).filter fun x => f x = y).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf y)
    _ = _ := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp

def reduction (n d : ℕ) : ZMod (n*d) →+* ZMod d :=
  ZMod.castHom (dvd_mul_left d n) (ZMod d)

theorem reduction_fibre_card (n d : ℕ) [NeZero n] [NeZero d] (y : ZMod d) :
    ((Finset.univ : Finset (ZMod (n*d))).filter fun x => reduction n d x = y).card = n := by
  have hf : Function.Surjective (reduction n d) :=
    ZMod.castHom_surjective (dvd_mul_left d n)
  have hc := card_mul_fibre (reduction n d).toAddMonoidHom hf y
  simp only [ZMod.card] at hc
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos d)
  convert hc.trans (Nat.mul_comm n d) using 1
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem reduction_preimage_card (n d : ℕ) [NeZero n] [NeZero d] (S : Finset (ZMod d)) :
    ((Finset.univ : Finset (ZMod (n*d))).filter fun x => reduction n d x ∈ S).card =
      S.card * n := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  simp only [reduction_fibre_card, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
