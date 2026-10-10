import OAI.NumberTheory.Ostmann.Characters.PrimeResidueCost

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.PrimeDyadicCover
open Preliminaries

abbrev Index (N : ℕ) := Fin (Nat.log 2 N+1)

def lower (Q N : ℕ) (i : Index N) : ℕ := Q*2^i.val

theorem lower_ge (Q N : ℕ) (i : Index N) : Q ≤ lower Q N i := by
  unfold lower
  exact Nat.le_mul_of_pos_right _ (by positivity)

theorem covers {Q N p : ℕ} (hQ : 0 < Q) (hp : Q ≤ p) (hpN : p ≤ N) :
    ∃ i : Index N, lower Q N i ≤ p ∧ p ≤ 2*lower Q N i := by
  let i := Nat.log 2 (p/Q)
  have hi : i ≤ Nat.log 2 N := Nat.log_mono_right ((Nat.div_le_self p Q).trans hpN)
  refine ⟨⟨i,by omega⟩,?_,?_⟩
  · change Q*2^i ≤ p
    calc
      _ ≤ Q*(p/Q) := Nat.mul_le_mul_left Q (Nat.pow_log_le_self 2 (Nat.div_pos hp hQ).ne')
      _ ≤ p := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self p Q
  · have hu : p/Q < 2^(i+1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hu' : p < 2^(i+1)*Q := (Nat.div_lt_iff_lt_mul hQ).mp hu
    change p ≤ 2*(Q*2^i)
    have he : 2^(i+1)*Q = 2*(Q*2^i) := by rw [pow_succ]; ring
    exact (he ▸ hu').le

theorem prime_shell_covers {Q N : ℕ} (hQ : 0 < Q) (E : Finset (PrimeUpTo N))
    (hmin : ∀ p ∈ E, Q ≤ p.val) :
    ∀ p ∈ E, ∃ i : Index N, lower Q N i ≤ p.val ∧ p.val ≤ 2*lower Q N i := by
  intro p hp
  exact covers hQ (hmin p hp) (Nat.mem_primesLE.mp p.property).1

theorem prime_coprime_of_lt {Q p : ℕ} (hQ : 0 < Q) (hp : p.Prime) (hlt : Q < p) :
    p.Coprime Q := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hQ hd)

theorem card_le_log (N : ℕ) :
    (Fintype.card (Index N):ℝ) ≤ Real.log N/Real.log 2+1 := by
  simp only [Index,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  exact add_le_add (by simpa only [Real.logb,Nat.cast_ofNat] using Real.natLog_le_logb N 2) le_rfl

theorem card_le_exp {N : ℕ} {β L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hN : Real.log N ≤ Real.exp (β*L)) :
    (Fintype.card (Index N):ℝ) ≤ (1/Real.log 2+1)*Real.exp (β*L) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (β*L) := Real.one_le_exp (mul_nonneg hβ hL)
  calc
    _ ≤ Real.log N/Real.log 2+1 := card_le_log N
    _ ≤ Real.exp (β*L)/Real.log 2+Real.exp (β*L) :=
      add_le_add (div_le_div_of_nonneg_right hN hl2.le) he
    _ = _ := by ring

end Ostmann.Characters.PrimeDyadicCover

end

end OAI
