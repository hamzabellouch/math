import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageScale
import OAI.Probability.SKBarriers.Dynamics.GreedyNumerics
import OAI.Probability.SKBarriers.Dynamics.BankCardinality

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

def scheduledBankSize (c : ℕ → ℝ) (B n : ℕ) {p : ℕ} (j : Fin p) : ℕ :=
  ⌈Real.exp ((c (j.val%B)+1)*levelLogScale n)⌉₊

 theorem scheduledBankSize_pos (c : ℕ → ℝ) (B n : ℕ) {p : ℕ} (j : Fin p) :
    0<scheduledBankSize c B n j := Nat.ceil_pos.mpr (Real.exp_pos _)

 theorem eventually_exp_dominates_linear (A : ℝ) :
    ∀ᶠ n : ℕ in atTop,A*levelLogScale n≤Real.exp (levelLogScale n) := by
  have H := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 zero_lt_one).comp stretchedLogScale_tendsto).const_mul A
  have H0 : Tendsto (fun n => A*levelLogScale n*Real.exp (-levelLogScale n)) atTop (𝓝 0) := by
    simpa only [levelLogScale,Real.rpow_one,neg_one_mul,mul_assoc,mul_zero,Function.comp_apply] using H
  filter_upwards [H0.eventually_le_const zero_lt_one] with n hn
  have HH := mul_le_mul_of_nonneg_right hn (Real.exp_pos (levelLogScale n)).le
  simpa only [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] using HH

 theorem greedy_level_count_bound {B : ℕ} (hB : 0<B) {t : ℝ} (ht : 0<t) (n : ℕ) :
    (B*greedyBlockCount B t n:ℕ)≤(t/8)*levelLogScale n := by
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  have H := mul_le_mul_of_nonneg_left (Nat.floor_le (show 0≤(t/(8*B))*levelLogScale n by unfold levelLogScale; positivity)) hb.le
  change (B:ℝ)*(greedyBlockCount B t n:ℝ)≤(B:ℝ)*((t/(8*B))*levelLogScale n) at H
  rw [Nat.cast_mul]
  convert H using 1
  field_simp

 theorem bank_miss_exp_bound (c L : ℝ) (_index : ℕ) :
    Real.exp (-(Real.exp (-c*L))*(⌈Real.exp ((c+1)*L)⌉₊:ℝ))≤Real.exp (-Real.exp L) := by
  have HK : Real.exp ((c+1)*L)≤(⌈Real.exp ((c+1)*L)⌉₊:ℝ) := Nat.le_ceil _
  apply Real.exp_le_exp.mpr
  have H := mul_le_mul_of_nonneg_left HK (Real.exp_pos (-c*L)).le
  have he : Real.exp (-c*L)*Real.exp ((c+1)*L)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at H
  linarith only [H]

 theorem scheduled_bank_coverage_sum {p B n : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j)
    (hL : 1≤levelLogScale n)
    (hdom : (bankPrefix c B+5)*levelLogScale n≤Real.exp (levelLogScale n)) :
    (∑j : Fin p,(Fintype.card (BankTuple (scheduledBankSize c B n) (blockPrior p B) j):ℝ)*
      (Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n)+
        Real.exp (-(Real.exp (-c (j.val%B)*levelLogScale n))*(scheduledBankSize c B n j))))≤
      2*p*Real.exp (-5*levelLogScale n) := by
  have hK (j : Fin p) : (scheduledBankSize c B n j:ℝ)≤Real.exp ((c (j.val%B)+2)*levelLogScale n) := ceil_exp_bound (hc _) hL
  calc
    _ ≤ ∑_j : Fin p,2*Real.exp (-5*levelLogScale n) := by
      apply Finset.sum_le_sum
      intro j _
      have HA := bankTuple_card_bound hB c (scheduledBankSize c B n) (levelLogScale n) hK j
      have hAj : bankPrefix c (j.val%B)≤bankPrefix c B := bankPrefix_mono c hc (Nat.mod_lt _ hB).le
      have Hmiss : Real.exp (-(Real.exp (-c (j.val%B)*levelLogScale n))*(scheduledBankSize c B n j))≤
          Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n) := by
        refine (bank_miss_exp_bound (c (j.val%B)) (levelLogScale n) 0).trans ?_
        apply Real.exp_le_exp.mpr
        have HH := mul_le_mul_of_nonneg_right (add_le_add hAj (le_refl (5:ℝ))) (by linarith only [hL])
        linarith only [HH,hdom]
      have H := mul_le_mul HA (add_le_add (le_refl (Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n))) Hmiss) (by positivity) (Real.exp_pos _).le
      refine H.trans_eq ?_
      rw [← two_mul,mul_comm (Real.exp _) (2*_),mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

 theorem scheduled_bank_locking_cost {p B n : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j)
    (hL : 5≤levelLogScale n) (hp : (p:ℝ)≤Real.exp (levelLogScale n)) {v : ℝ}
    (hv0 : 0≤v) (hv : v≤Real.exp (-(3*bankPrefix c B+20)*levelLogScale n)) :
    (8*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^3+
      48*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^2)*v≤Real.exp (-4*levelLogScale n) := by
  let A := bankPrefix c B
  let L := levelLogScale n
  let N : ℝ := Fintype.card (BankIndex (scheduledBankSize c B n (p:=p)))
  have hA : 0≤A := bankPrefix_nonneg c hc B
  have hL0 : 0≤L := by dsimp only [L]; linarith only [hL]
  have hN0 : 0≤N := Nat.cast_nonneg _
  have hN : N≤Real.exp ((A+1)*L) := by
    refine (bankIndex_card_bound hB c hc (scheduledBankSize c B n) hL0
      (fun j => ceil_exp_bound (hc _) (by linarith only [hL]))).trans ?_
    calc
      _ ≤ Real.exp L*Real.exp (A*L) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he1 : 1≤Real.exp ((A+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
  have HN3 : N^3≤Real.exp (3*(A+1)*L) := by
    have H := pow_le_pow_left₀ hN0 hN 3
    simpa only [← Real.exp_nat_mul,Nat.cast_ofNat,mul_assoc] using H
  have HN2 : N^2≤Real.exp (3*(A+1)*L) := by
    have H := pow_le_pow_left₀ hN0 hN 2
    have HH : (Real.exp ((A+1)*L))^2≤(Real.exp ((A+1)*L))^3 := pow_le_pow_right₀ he1 (by decide)
    exact (H.trans HH).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have HC : (8*N^3+48*N^2)*v≤56*Real.exp (-17*L) := by
    calc
      _ ≤ (56*Real.exp (3*(A+1)*L))*Real.exp (-(3*A+20)*L) :=
        mul_le_mul (by linarith only [HN3,HN2]) hv hv0 (by positivity)
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have HE56 : (56:ℝ)≤Real.exp (13*L) := by
    have H := Real.add_one_le_exp (13*L)
    dsimp only [L] at H
    linarith only [H,hL]
  refine HC.trans ?_
  calc
    _ ≤ Real.exp (13*L)*Real.exp (-17*L) := mul_le_mul_of_nonneg_right HE56 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SK.Analytic

end
end

end OAI
