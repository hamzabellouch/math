import Mathlib
import OAI.Combinatorics.SharpRamsey.Validation.ValidationSchedule

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma geom_card_le {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    ∑ i ∈ range r,q^i ≤ q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ,pow_succ]
    calc
      _ ≤ q^r+q^r := Nat.add_le_add_right ih _
      _ = q^r*2 := (Nat.mul_two _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hq

lemma projective_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype (Projectivization K V)]
    (r : ℕ) (hdim : Module.finrank K V=r) :
    log ((Fintype.card (Projectivization K V):ℝ)+1) ≤ ((r:ℝ)+1)*Nat.card K := by
  have hqN : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast hqN.trans' (by norm_num : 1 ≤ 2)
  have hq0 : (0:ℝ) < Nat.card K := by linarith
  have hcard : (Fintype.card (Projectivization K V):ℝ) ≤ (Nat.card K:ℝ)^r := by
    have hn : Fintype.card (Projectivization K V) ≤ Nat.card K^r := by
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
      exact geom_card_le hqN r
    exact_mod_cast hn
  have hpow : 1 ≤ (Nat.card K:ℝ)^r := one_le_pow₀ hq
  have hs : (Fintype.card (Projectivization K V):ℝ)+1 ≤ 2*(Nat.card K:ℝ)^r := by linarith
  apply (log_le_log (by positivity) hs).trans
  rw [log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow]
  have hl2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hlq : log (Nat.card K:ℝ) ≤ Nat.card K :=
    (log_le_sub_one_of_pos hq0).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hlq (show 0 ≤ (r:ℝ) by positivity)
  linarith

lemma pair_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype (Projectivization K V)]
    [Fintype (Projectivization K (Module.Dual K V))]
    (r : ℕ) (hdim : Module.finrank K V=r) :
    log (((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2+1) ≤
      (2*(r:ℝ)+2)*Nat.card K := by
  have hA := projective_log_card r hdim
  have hB := projective_log_card (K:=K) (V:=Module.Dual K V) r
    (Subspace.dual_finrank_eq.trans hdim)
  let A : ℝ := Fintype.card (Projectivization K V)
  let B : ℝ := Fintype.card (Projectivization K (Module.Dual K V))
  have ha : 0 ≤ A := by positivity
  have hb : 0 ≤ B := by positivity
  have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hu2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hh : (A+B)*log 2+1 ≤ (A+1)*(B+1) := by nlinarith [mul_nonneg ha hb]
  have hl := log_le_log (by positivity : 0 < (A+B)*log 2+1) hh
  rw [log_mul (by positivity) (by positivity)] at hl
  change log ((A+B)*log 2+1) ≤ _
  change log (A+1) ≤ _ at hA
  change log (B+1) ≤ _ at hB
  linarith

lemma row_cost {q P d B H C J : ℝ} {h : ℕ}
    (hq : 1 ≤ q) (hP : 1 ≤ P) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hBP : B ≤ C*P)
    (hh : (h:ℝ) ≤ 20*q*(d+2)+1) (hH : log (H+1) ≤ J*q) :
    2*((h:ℝ)*B+log 2+log (H+1))+log 3 ≤
      (100*C+2*J+10)*q*P*(d+P) := by
  have hu2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hu3 : log (3:ℝ) ≤ 2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hh' : (h:ℝ) ≤ 21*q*(d+2) := by nlinarith
  have hmul := mul_le_mul hh' hBP hB (show 0 ≤ 21*q*(d+2) by positivity)
  have hdP : d+2 ≤ 2*(d+P) := by linarith
  have hmul' := mul_le_mul_of_nonneg_left hdP (show 0 ≤ 21*C*q*P by positivity)
  let v := q*P*(d+P)
  have hvq : q ≤ v := by
    have hp : 1 ≤ P*(d+P) := one_le_mul_of_one_le_of_one_le hP (by linarith)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ q by linarith)
    dsimp only [v]; nlinarith only [hh]
  have hv : 1 ≤ v := hq.trans hvq
  have hj := mul_le_mul_of_nonneg_left hvq hJ
  have hp : 0 ≤ C*v := by positivity
  dsimp only [v] at *
  nlinarith

lemma scheduleLength_le {q u t : ℝ} (hq : 0 ≤ q) (ht : 0 < t) (htu : t ≤ u) :
    (scheduleLength q u t:ℝ) ≤ 20*q*(log (u/t)+2)+1 := by
  have hl : 0 ≤ log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  exact (Nat.ceil_lt_add_one (by positivity)).le

end
end SharpLogRamsey.Validation

end

end OAI
