import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorRanges

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Finset

def dyadicDivisors (k : ℕ) : Finset ℕ := Ico (2^k) (2^(k+1))

def divisorDyadicDepth (D : ℕ) : ℕ := Nat.log 2 (2*D)+1

def divisorDyadicIndices (D : ℕ) : Finset (ℕ × ℕ) :=
  ((range (divisorDyadicDepth D)) ×ˢ range (divisorDyadicDepth D)).filter
    (fun k => D < 4*(2^k.1*2^k.2) ∧ 2^k.1*2^k.2 ≤ 2*D)

@[simp] theorem dyadicDivisors_card (k : ℕ) : (dyadicDivisors k).card=2^k := by
  simp [dyadicDivisors,Nat.card_Ico,pow_succ]
  omega

theorem mem_dyadicDivisors_log {d : ℕ} (hd : 0<d) :
    d∈dyadicDivisors (Nat.log 2 d) := by
  exact mem_Ico.mpr ⟨Nat.pow_log_le_self 2 hd.ne',Nat.lt_pow_succ_log_self (by decide) d⟩

theorem dyadic_pair_mem {D x y : ℕ} (hx : 0<x) (hy : 0<y)
    (hlo : D<x*y) (hhi : x*y≤2*D) :
    (Nat.log 2 x,Nat.log 2 y)∈divisorDyadicIndices D := by
  have hxD : x≤2*D := (Nat.le_mul_of_pos_right _ hy).trans hhi
  have hyD : y≤2*D := (Nat.le_mul_of_pos_left _ hx).trans hhi
  have hxL := Nat.pow_log_le_self 2 hx.ne'
  have hyL := Nat.pow_log_le_self 2 hy.ne'
  have hxU := Nat.lt_pow_succ_log_self (by decide : 1<2) x
  have hyU := Nat.lt_pow_succ_log_self (by decide : 1<2) y
  simp only [pow_succ] at hxU hyU
  have hu : x*y < 4*(2^(Nat.log 2 x)*2^(Nat.log 2 y)) := by
    have h1 := Nat.mul_lt_mul_of_pos_right hxU hy
    have h2 := Nat.mul_le_mul_left (2^(Nat.log 2 x)*2) hyU.le
    nlinarith
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) hxD)),mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) hyD))⟩,
    hlo.trans hu,(Nat.mul_le_mul hxL hyL).trans hhi⟩

theorem divisorDyadicIndices_nonempty {D : ℕ} (hD : 0<D) :
    (divisorDyadicIndices D).Nonempty := by
  refine ⟨(Nat.log 2 1,Nat.log 2 (D+1)),dyadic_pair_mem (by decide) (by omega) ?_ ?_⟩ <;> omega

theorem divisorDyadicIndices_card_le (D : ℕ) :
    (divisorDyadicIndices D).card≤(divisorDyadicDepth D)^2 := by
  exact (card_filter_le _ _).trans_eq (by simp [sq])

theorem divisorDyadicIndices_scales {D : ℕ} (_hD : 0<D) {k : ℕ × ℕ}
    (hk : k∈divisorDyadicIndices D) :
    0<2^k.1 ∧ 0<2^k.2 ∧ D<4*(2^k.1*2^k.2) ∧
      2^k.1*2^k.2≤2*D ∧ 2^k.1≤2*D ∧ 2^k.2≤2*D := by
  obtain ⟨hr,hlo,hhi⟩ := mem_filter.mp hk
  obtain ⟨h1,h2⟩ := mem_product.mp hr
  have hp1 : 0<2^k.1 := by positivity
  have hp2 : 0<2^k.2 := by positivity
  exact ⟨hp1,hp2,hlo,hhi,(Nat.le_mul_of_pos_right _ hp2).trans hhi,
    (Nat.le_mul_of_pos_left _ hp1).trans hhi⟩

end Ostmann.QuadraticSieve

end

end OAI
