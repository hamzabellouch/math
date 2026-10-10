import OAI.Dynamics.ConditionalShuffle.InstrumentChunks

namespace OAI

noncomputable section
open Filter Topology
namespace Revealed.Physical
open scoped Classical
open Thorp Thorp.Conditional Thorp.Specht Revealed.Split Revealed.Instrument

lemma eight_block_coset_ratio (d : ℕ) :
    2 * ((Fintype.card (State d) : ℝ) / Fintype.card (State (d+1+2))) < 1 := by
  have hm : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  have hf : 2 * (2^d).factorial < (2^(d+1+2)).factorial := by
    have h : 2 * (2^d).factorial < (2^d+2).factorial := by
      calc
        _ < (2^d+2) * (2^d).factorial := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.factorial_pos _)
        _ ≤ (2^d+2) * (2^d+1).factorial := Nat.mul_le_mul_left _ (Nat.factorial_le (by omega))
        _ = (2^d+2).factorial := (Nat.factorial_succ _).symm
    apply h.trans_le (Nat.factorial_le _)
    simp only [pow_add]
    norm_num
    omega
  have hc : (0 : ℝ) < Fintype.card (State (d+1+2)) := by exact_mod_cast Fintype.card_pos
  rw [← mul_div_assoc, div_lt_one hc]
  exact_mod_cast (by simpa only [State, Fintype.card_perm, card_position] using hf)

def fullConditionalRate (d : ℕ) : ℝ := 512 * conditionalRate d + (1/2 : ℝ) *
  Real.sqrt ((96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))

lemma fullConditionalRate_tendsto : Tendsto fullConditionalRate atTop (nhds 0) := by
  have he := Block.exceptional_cube_tendsto.comp (tendsto_add_atTop_nat 3)
  have hh := (conditionalRate_tendsto.const_mul 512).add
    (((he.const_mul ((96 : ℝ)^8)).sqrt).const_mul (1/2 : ℝ))
  change Tendsto (fun d : ℕ => 512 * conditionalRate d + (1/2 : ℝ) *
    Real.sqrt ((96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))) atTop (nhds 0)
  simpa only [Function.comp_def, Nat.add_assoc, mul_zero, Real.sqrt_zero, add_zero] using hh

lemma physical_distance_bound {ι : Type} [Fintype ι] (d : ℕ) (hd : 1 ≤ d)
    (hR : (permutationFamily (Position d)).reciprocalSum ≤ 3)
    (e : Outside ι (Position (d+1+2)) (Position (d+2+2))) :
    Instrument.distance (instrument (d+2+2)) e (3200*(d+2+2)) ≤ fullConditionalRate d := by
  have hn : 16 ≤ Fintype.card (Position (d+1+2)) := by
    rw [card_position]
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^(d+1+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let : Nontrivial (Position (d+1+2)) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let : Fintype (Outside ι (Position (d+1+2)) (Position (d+2+2))) := inferInstance
  let I := instrument (ι:=ι) (α:=Position (d+1+2)) (d+2+2)
  have hh := distance_eight_le (block I (400*(d+2+2))) hn
    (Block.embedding (Block.eightEquiv d)) (eight_block_coset_ratio d)
    (fun e p => block_kernel_dichotomy I
      (physical_kernel_dichotomy (d+2+1)) e (400*(d+2+2)) p)
    (16*conditionalRate d) (block_discarded_le d) e
  rw [distance_block] at hh
  have ht : 400*(d+2+2)*8 = 3200*(d+2+2) := by omega
  rw [ht] at hh
  apply hh.trans
  unfold fullConditionalRate
  have hp : (32*(permutationFamily (Position d)).reciprocalSum)^8 ≤ (96 : ℝ)^8 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) (permutationFamily (Position d)).reciprocalSum_nonneg)
      (by linarith only [hR]) 8
  have he : 0 ≤ exceptionalReciprocalSum (2^(d+1+2)) := by
    exact Finset.sum_nonneg (fun p _ => by
      change 0 ≤ (if 0 < defect p then inverseDegree p else 0)
      split_ifs <;> first | exact inverseDegree_nonneg p | exact le_rfl)
  rw [card_position]
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hp he)
  rw [show (32 : ℝ) * (16 * conditionalRate d) = 512 * conditionalRate d by ring]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1/2))

lemma physical_distance_eventually {ι : ℕ → Type} [∀ d, Fintype (ι d)] :
    ∀ᶠ d in atTop, ∀ e : Outside (ι d) (Position (d+1+2)) (Position (d+2+2)),
      Instrument.distance (instrument (d+2+2)) e (3200*(d+2+2)) ≤ fullConditionalRate d := by
  filter_upwards [Block.reciprocal_atMost_three, eventually_ge_atTop 1] with d hR hd e
  exact physical_distance_bound d hd hR e

end Revealed.Physical

end

end OAI
