import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPriorRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedPrior
open scoped BigOperators
open PrimeDyadicCover
attribute [local instance] Classical.propDecidable

def block (Q U : ℕ) (S : Finset ℕ) (i : Index U) : Finset ℕ :=
  S.filter (fun p=>Nat.log 2 (p/Q)=i.val)

theorem block_subset (Q U : ℕ) (S : Finset ℕ) (i : Index U) : block Q U S i⊆S :=
  Finset.filter_subset _ _

theorem sum_blocks_eq {A : Type*} [AddCommMonoid A] (Q U : ℕ) (S : Finset ℕ)
    (hS : ∀p∈S,p≤U) (f : ℕ→A) :
    (∑i:Index U,∑p∈block Q U S i,f p)=∑p∈S,f p := by
  simp only [block,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hi : Nat.log 2 (p/Q)<Nat.log 2 U+1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right ((Nat.div_le_self p Q).trans (hS p hp)))
  have he (i : Index U) : Nat.log 2 (p/Q)=i.val ↔ i=⟨Nat.log 2 (p/Q),hi⟩ := by
    constructor
    · intro hh
      exact Fin.ext hh.symm
    · rintro rfl
      rfl
  simp_rw [he]
  simp

theorem block_bounds {Q U : ℕ} (hQ : 0<Q) (S : Finset ℕ)
    (hmin : ∀p∈S,Q≤p) (i : Index U) {p : ℕ} (hp : p∈block Q U S i) :
    lower Q U i≤p ∧ p≤2*lower Q U i := by
  obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
  have hpQ := hmin p hp
  constructor
  · change Q*2^i.val≤p
    rw [←hi]
    calc
      _ ≤ Q*(p/Q) := Nat.mul_le_mul_left Q (Nat.pow_log_le_self 2 (Nat.div_pos hpQ hQ).ne')
      _ ≤ p := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self p Q
  · have hu : p/Q<2^(i.val+1) := by
      rw [←hi]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hu' : p<2^(i.val+1)*Q := (Nat.div_lt_iff_lt_mul hQ).mp hu
    change p≤2*(Q*2^i.val)
    have he : 2^(i.val+1)*Q=2*(Q*2^i.val) := by rw [pow_succ]; ring
    exact (he ▸ hu').le

theorem block_lower_pos {Q U : ℕ} (hQ : 0<Q) (i : Index U) : 0<lower Q U i :=
  hQ.trans_le (lower_ge Q U i)

theorem sum_block_rows_eq {A : Type*} [AddCommMonoid A]
    (Q U : ℕ) (hQ : 0<Q) (S : Finset ℕ)
    (hmin : ∀p∈S,Q≤p) (hmax : ∀p∈S,p≤U) (f : ℕ→A) :
    (∑i:Index U,∑x:Fin Q × Fin (2*lower Q U i+1),
      if rowValue Q (2*lower Q U i+1) x∈block Q U S i then
        f (rowValue Q (2*lower Q U i+1) x) else 0)=∑p∈S,f p := by
  calc
    _ = ∑i:Index U,∑p∈block Q U S i,f p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_rows_eq Q (lower Q U i) hQ (block Q U S i)
        (fun p hp=>(block_bounds hQ S hmin i hp).2) f
    _ = _ := sum_blocks_eq Q U S hmax f

end Ostmann.Characters.TemplateOneSidedPrior

end

end OAI
