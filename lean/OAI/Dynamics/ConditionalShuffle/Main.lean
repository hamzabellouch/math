import OAI.Dynamics.ConditionalShuffle.ConditionalMixing

namespace OAI

noncomputable section
open Filter Topology
namespace Thorp

lemma distance_antitone (d : ℕ) : Antitone (distance d) := by
  apply antitone_nat_of_succ_le
  intro t
  unfold distance uniform
  rw [law_add]
  have hh := FiniteLaw.tv_conv_contract (law d 1) (law d t)
    (law_sum d 1) (law_sum d t) 0 (law_nonneg d 1)
  simpa only [mul_zero, sub_zero, one_mul] using hh

lemma full_mixing_time {T : ℕ → ℕ} (hT : ∀ᶠ d in atTop, 1600*d ≤ T d) :
    Tendsto (fun d : ℕ => distance d (T d)) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun d => by unfold distance tv; positivity))
    _ full_mixing
  filter_upwards [hT] with d hd
  exact distance_antitone d hd

lemma full_mixing_constant (C : ℕ) (hC : 1600 ≤ C) :
    Tendsto (fun d : ℕ => distance d (C*d)) atTop (nhds 0) :=
  full_mixing_time (Eventually.of_forall (fun d => Nat.mul_le_mul_right d hC))

lemma support_lower_every_time (d t : ℕ) (hd : 1 ≤ d) :
    1 - (2 : ℝ)^(t*2^(d-1)) / ((2^d).factorial : ℝ) ≤ distance d t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, mul_comm] using distance_support_lower k t

end Thorp
namespace Revealed
open Thorp

lemma twoHalfC_pos : 0 < twoHalfC := by
  have hx : 0 < (3 + twoHalfP) / 4 := by norm_num [twoHalfP, twoHalfL]
  have hy : (3 + twoHalfP) / 4 < 1 := by norm_num [twoHalfP, twoHalfL]
  have hh : Real.logb 2 ((3 + twoHalfP) / 4) < 0 :=
    Real.logb_neg (by norm_num) hx hy
  unfold twoHalfC
  linarith

lemma twoHalfC_lt_one : twoHalfC < 1 := by
  have hx : (1 : ℝ)/2 < (3 + twoHalfP) / 4 := by norm_num [twoHalfP, twoHalfL]
  have hh := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<1/2) hx
  have hl : Real.logb (2:ℝ) (1/2) = -1 := by simp
  rw [hl] at hh
  unfold twoHalfC
  linarith

lemma twoHalfB_ge_four : 4 ≤ twoHalfB := by
  have h : (4:ℝ) ≤ 10 / twoHalfC := by
    rw [le_div_iff₀ twoHalfC_pos]
    linarith [twoHalfC_lt_one]
  exact (by exact_mod_cast h.trans (Nat.le_ceil _))

theorem main :
    Tendsto (fun d : ℕ => worstConditionalTV d (40000 * (400 + 1) * (d + 1)))
      atTop (nhds 0) ∧
    Tendsto (fun d : ℕ => distance d (16040400 * d)) atTop (nhds 0) ∧
    (∀ (d t : ℕ) (g₀ : State d),
      tv (lawFrom d t g₀) (uniform d) = distance d t) ∧
    (∀ (d t : ℕ), 1 ≤ d →
      1 - (2 : ℝ) ^ (t * 2 ^ (d - 1)) / ((2 ^ d).factorial : ℝ) ≤ distance d t) ∧
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ)) orderFunction ∧
    Tendsto (fun d : ℕ => distance d (171798691968 * d)) atTop (nhds 0) ∧
    Tendsto (fun d : ℕ => distance d (33030144 * d)) atTop (nhds 0) ∧
    Tendsto (fun d : ℕ => distance d (400 * twoHalfB * d)) atTop (nhds 0) := by
  refine ⟨conditional_mixing, full_mixing_constant _ (by norm_num), worst_start_eq,
    support_lower_every_time, mixingTime_isTheta_orderFunction,
    full_mixing_constant _ (by norm_num), full_mixing_constant _ (by norm_num), ?_⟩
  exact full_mixing_constant _ (by have h := twoHalfB_ge_four; omega)

end Revealed

end

end OAI
