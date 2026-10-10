import Mathlib
import OAI.Combinatorics.SharpRamsey.Bounds.SumFiberCenter

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
open scoped BigOperators
namespace SharpLogRamsey.Upper
theorem sampling_parameter {h m t : ℝ} (hh : 1 ≤ h) (hm : 1 ≤ m)
    (ht : 65536 ≤ t) (hratio : m * Real.sqrt t ≤ h) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ 1 ≤ p*h ∧ p^2*h*m ≤ 1/8 ∧
      Real.log t ≤ 8 * Real.log (p*h) := by
  have hh0 : 0 < h := by linarith
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt (h*m) := Real.sqrt_pos.mpr (mul_pos hh0 hm0)
  let p := 1 / (4 * Real.sqrt (h*m))
  have hp : 0 < p := by dsimp [p]; positivity
  have hs1 : 1 ≤ Real.sqrt (h*m) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hsq := Real.sq_sqrt (show 0 ≤ h*m by positivity)
  have hmoment : p^2*h*m = 1/16 := by
    dsimp [p]
    field_simp
    nlinarith
  have hlog : Real.log (p*h) = (Real.log h - Real.log m)/2 - Real.log 4 := by
    dsimp [p]
    rw [Real.log_mul (by positivity) hh0.ne', Real.log_div (by norm_num) (by positivity),
      Real.log_one, Real.log_mul (by norm_num) hs.ne', Real.log_sqrt (by positivity : 0 ≤ h*m),
      Real.log_mul hh0.ne' hm0.ne']
    ring
  have hratio' := Real.log_le_log (mul_pos hm0 (Real.sqrt_pos.mpr ht0)) hratio
  rw [Real.log_mul hm0.ne' (Real.sqrt_pos.mpr ht0).ne', Real.log_sqrt ht0.le] at hratio'
  have htlog := Real.log_le_log (show (0:ℝ) < 65536 by norm_num) ht
  have h65536 : Real.log (65536:ℝ) = 8 * Real.log 4 := by
    rw [show (65536:ℝ) = 4^8 by norm_num, Real.log_pow]
    norm_num
  rw [h65536] at htlog
  have hl : Real.log t ≤ 8 * Real.log (p*h) := by linarith
  have hl0 : 0 ≤ Real.log (p*h) := by
    have htl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  have hph : 1 ≤ p*h := by
    exact (Real.log_nonneg_iff (by positivity)).mp hl0
  exact ⟨p,hp,hp1,hph,by linarith,hl⟩

end SharpLogRamsey.Upper

namespace SharpLogRamsey.Upper
open Foundation Sampling
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem alteration_bound {h m t : ℕ} (ht : 1 ≤ t)
    (hG : Gᶜ.CliqueFree t) (hdeg : ∀ x, G.degree x ≤ h)
    (hcommon : ∀ x y, G.Adj x y → Fintype.card (G.commonNeighbors x y) ≤ m)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hph : 1 ≤ p*h) (hmoment : p^2*h*m ≤ 1/8) :
    (Fintype.card V : ℝ) * Real.log (p*h) ≤ 256 * t * h := by
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hhp : (0:ℝ) < h := by nlinarith
  have hD : 0 < 12*p*h := by positivity
  obtain ⟨U,hU,hUd,hUt⟩ := sample_prune G hp.le hp1 hD
  have hsum : (∑ x : V, (G.degree x : ℝ)) ≤ n*h := by
    calc
      _ ≤ ∑ _x : V, (h : ℝ) := sum_le_sum (fun x _ => by exact_mod_cast hdeg x)
      _ = n*h := by simp [n]
  have htri : ((G.cliqueFinset 3).card : ℝ) ≤ n*h*m := by
    dsimp [n]
    exact_mod_cast triangle_count_le G hdeg hcommon
  have hloss : p^2 * (∑ x : V, (G.degree x : ℝ)) / (12*p*h) ≤ n*p/12 := by
    apply (div_le_iff₀ hD).mpr
    calc
      _ ≤ p^2*(n*h) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = n*p/12*(12*p*h) := by ring
  have htri' : p^3 * ((G.cliqueFinset 3).card : ℝ) ≤ n*p/8 := by
    calc
      _ ≤ p^3*(n*h*m) := mul_le_mul_of_nonneg_left htri (by positivity)
      _ = n*p*(p^2*h*m) := by ring
      _ ≤ n*p*(1/8) := mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = n*p/8 := by ring
  have hUsize : 3/4*n*p ≤ (U.card : ℝ) := by dsimp [n] at *; linarith
  have hlog : 0 ≤ Real.log (p*h) := Real.log_nonneg hph
  by_cases hn0 : n = 0
  · change n * _ ≤ _
    rw [hn0, zero_mul]
    positivity
  have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
  have hUpos : 0 < U.card := by
    have hu : (0:ℝ) < U.card := lt_of_lt_of_le (by positivity) hUsize
    exact_mod_cast hu
  obtain ⟨x,hx⟩ := card_pos.mp hUpos
  let : Nonempty (U : Set V) := ⟨⟨x,hx⟩⟩
  have ha := TriangleFree.indepNum_lower_bound (G.induce (U : Set V)) hUt
    (by nlinarith : (1:ℝ) ≤ 12*p*h) hUd
  have hat : ((G.induce (U : Set V)).indepNum : ℝ) < t := by
    exact_mod_cast indepNum_lt_of_cliqueFree_compl (G.induce (U : Set V))
      (compl_cliqueFree_induce G hG _)
  have ha' : (U.card : ℝ) * Real.log (12*p*h+1) < t*(8*(12*p*h+1)) := by
    have H := ha.trans_lt hat
    rw [div_lt_iff₀ (by positivity)] at H
    have hc : Fintype.card (U : Set V) = U.card := Fintype.card_coe U
    simpa only [hc] using H
  have hl : Real.log (p*h) ≤ Real.log (12*p*h+1) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hu : (3/4*n*p) * Real.log (p*h) ≤
      (U.card : ℝ) * Real.log (12*p*h+1) :=
    mul_le_mul hUsize hl hlog (Nat.cast_nonneg _)
  have hd : t*(8*(12*p*h+1)) ≤ 104*t*p*h := by
    have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hph ht0]
  have H := (hu.trans_lt ha').trans_le hd
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  change n*Real.log (p*h) ≤ _
  have : p*(n*Real.log (p*h)) ≤ p*(256*t*h) := by nlinarith
  exact (mul_le_mul_iff_right₀ hp).mp this

theorem graph_recurrence (j : ℕ) {t : ℕ} (ht : 65536 ≤ t)
    (hs : G.CliqueFree (j+4)) (hi : Gᶜ.CliqueFree t) :
    (Fintype.card V : ℝ) ≤
      t*((t:ℝ)^(j+1)*Real.sqrt t+1) +
        2048*t*(ramsey (j+3) t)/Real.log t := by
  let h := G.maxDegree
  let m := ramsey (j+2) t
  have ht1 : 1 ≤ t := by omega
  have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hm1 : 1 ≤ m := ht1.trans (le_ramsey (by omega) ht1)
  have hmb : (m : ℝ) ≤ (t:ℝ)^(j+1) := by
    have H := ramsey_le_pow (s := j+2) (by omega) ht1
    norm_num at H
    exact_mod_cast H
  have hcommon : ∀ x y, G.Adj x y → Fintype.card (G.commonNeighbors x y) ≤ m := by
    intro x y hxy
    exact (order_lt_ramsey (G.induce (G.commonNeighbors x y)) (by omega) ht1
      (cliqueFree_common G hs hxy) (compl_cliqueFree_induce G hi _)).le
  have hdeg : ∀ x, G.degree x ≤ h := G.degree_le_maxDegree
  have hhr : h ≤ ramsey (j+3) t := by
    apply G.maxDegree_le_of_forall_degree_le
    intro x
    have H := order_lt_ramsey (G.induce (G.neighborSet x)) (by omega) ht1
      (cliqueFree_neighbor G hs x) (compl_cliqueFree_induce G hi _)
    rw [G.card_neighborSet_eq_degree] at H
    exact H.le
  have hright : 0 ≤ 2048*(t:ℝ)*(ramsey (j+3) t)/Real.log t := by positivity
  by_cases hsmall : (h:ℝ) ≤ m*Real.sqrt t
  · have hn := card_le_mul_indepNum G (B := h+1) (by intro x; exact Nat.add_le_add_right (hdeg x) 1)
    have hia := indepNum_lt_of_cliqueFree_compl G hi
    have Hnat : Fintype.card V ≤ (h+1)*t := hn.trans (Nat.mul_le_mul_left _ hia.le)
    have H : (Fintype.card V : ℝ) ≤ ((h:ℝ)+1)*t := by exact_mod_cast Hnat
    have hm' := mul_le_mul_of_nonneg_right hmb (Real.sqrt_nonneg (t:ℝ))
    have H' := mul_le_mul_of_nonneg_right (add_le_add_right (hsmall.trans hm') 1) ht0.le
    nlinarith
  · have hh : (1:ℝ) ≤ h := by
      have hsqrt : 1 ≤ Real.sqrt (t:ℝ) := by
        rw [Real.le_sqrt (by norm_num) ht0.le]
        exact_mod_cast ht1
      have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
      nlinarith
    obtain ⟨p,hp,hp1,hph,hpm,hl⟩ := sampling_parameter hh (by exact_mod_cast hm1)
      (by exact_mod_cast ht) (le_of_not_ge hsmall)
    have hab := alteration_bound G ht1 hi hdeg hcommon hp hp1 hph hpm
    have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have H : (Fintype.card V : ℝ)*Real.log t ≤ 2048*t*h := by
      nlinarith [mul_le_mul_of_nonneg_left hl hn0]
    have H' : (Fintype.card V : ℝ) ≤ 2048*t*h/Real.log t :=
      (le_div_iff₀ hlog).mpr H
    have H'' : 2048*(t:ℝ)*h/Real.log t ≤ 2048*t*(ramsey (j+3) t)/Real.log t := by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hhr) (by positivity)
    have hleft : 0 ≤ (t:ℝ)*((t:ℝ)^(j+1)*Real.sqrt t+1) := by positivity
    linarith

theorem ramsey_recurrence (j : ℕ) {t : ℕ} (ht : 65536 ≤ t) :
    (ramsey (j+4) t : ℝ) ≤
      t*((t:ℝ)^(j+1)*Real.sqrt t+1) +
        2048*t*(ramsey (j+3) t)/Real.log t + 1 := by
  classical
  obtain ⟨G,hG,hGi⟩ := exists_avoiding_pred (s := j+4) (by omega) (by omega : 2 ≤ t)
  have H := graph_recurrence G j ht hG hGi
  simp only [Fintype.card_fin] at H
  have hr : 1 ≤ ramsey (j+4) t :=
    (by omega : 1 ≤ t).trans (le_ramsey (by omega) (by omega))
  rw [Nat.cast_sub hr, Nat.cast_one] at H
  linarith

theorem ramsey_three {t : ℕ} (ht : 2 ≤ t) :
    (ramsey 3 t : ℝ)*Real.log t ≤ 17*(t:ℝ)^2 := by
  classical
  obtain ⟨G,hG,hGi⟩ := exists_avoiding_pred (s := 3) (by omega) ht
  have hr : 2 ≤ ramsey 3 t := ht.trans (le_ramsey (by omega) (by omega))
  have hnon : 0 < ramsey 3 t - 1 := by omega
  let : Nonempty (Fin (ramsey 3 t - 1)) := Fin.pos_iff_nonempty.mp hnon
  have hd : ∀ x, (G.degree x : ℝ) ≤ t := by
    intro x
    have H := order_lt_ramsey (G.induce (G.neighborSet x)) (by omega : 2 ≤ 2)
      (by omega : 1 ≤ t) (cliqueFree_neighbor G hG x) (compl_cliqueFree_induce G hGi _)
    rw [G.card_neighborSet_eq_degree, ramsey_two (by omega)] at H
    exact_mod_cast H.le
  have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hl : 0 ≤ Real.log (t:ℝ) := Real.log_nonneg ht1
  have H := TriangleFree.indepNum_lower_bound G hG ht1 hd
  have hi : (G.indepNum : ℝ) < t := by
    exact_mod_cast indepNum_lt_of_cliqueFree_compl G hGi
  have H' := H.trans_lt hi
  rw [div_lt_iff₀ (by positivity)] at H'
  have hc : (Fintype.card (Fin (ramsey 3 t - 1)) : ℝ) = (ramsey 3 t : ℝ)-1 := by
    rw [Fintype.card_fin, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at H'
  have hl' : Real.log (t:ℝ) ≤ Real.log ((t:ℝ)+1) := Real.log_le_log ht0 (by linarith)
  have hn : 0 ≤ (ramsey 3 t : ℝ)-1 := by
    have H : (2:ℝ) ≤ ramsey 3 t := by exact_mod_cast hr
    linarith
  have hh := mul_le_mul_of_nonneg_left hl' hn
  have hlt := Real.log_le_self ht0.le
  nlinarith [sq_nonneg ((t:ℝ)-1)]

open Filter in
 theorem eventually_log_pow_le_sqrt (j : ℕ) :
    ∀ᶠ t : ℕ in atTop, (Real.log (t:ℝ))^j ≤ Real.sqrt t := by
  have H := (isLittleO_log_rpow_rpow_atTop (j:ℝ) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  have Hn := tendsto_natCast_atTop_atTop.eventually H
  filter_upwards [Hn, eventually_ge_atTop (1:ℕ)] with t ht ht1
  have hlog := Real.log_nonneg (show (1:ℝ) ≤ t by exact_mod_cast ht1)
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog _),
    ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _), one_mul] using ht

open Filter in

 theorem ramsey_upper_scaled (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      (ramsey (j+3) t : ℝ)*(Real.log (t:ℝ))^(j+1) ≤ C*(t:ℝ)^(j+2) := by
  induction j with
  | zero =>
    refine ⟨17, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (2:ℕ)] with t ht
    simpa using ramsey_three ht
  | succ j ih =>
    obtain ⟨C,hC,hCb⟩ := ih
    refine ⟨3+2048*C, by positivity, ?_⟩
    filter_upwards [hCb, eventually_log_pow_le_sqrt (j+2),
      eventually_ge_atTop (65536:ℕ)] with t hCt hL ht
    have ht1 : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    have ht0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hl : 0 < Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    have hs := Real.sqrt_nonneg (t:ℝ)
    have hs2 := Real.sq_sqrt ht0.le
    have hst : Real.sqrt (t:ℝ) ≤ t := by
      rw [Real.sqrt_le_iff]
      exact ⟨ht0.le, by nlinarith⟩
    have hpow : (t:ℝ)^2 ≤ (t:ℝ)^(j+3) := pow_le_pow_right₀ ht1 (by omega)
    have hsmall : (t*((t:ℝ)^(j+1)*Real.sqrt t+1)+1)*(Real.log (t:ℝ))^(j+2) ≤
        3*(t:ℝ)^(j+3) := by
      calc
        _ ≤ (t*((t:ℝ)^(j+1)*Real.sqrt t+1)+1)*Real.sqrt t :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        _ = (t:ℝ)^(j+1)*t*(Real.sqrt t)^2+(t+1)*Real.sqrt t := by ring
        _ = (t:ℝ)^(j+3)+(t+1)*Real.sqrt t := by
          rw [hs2]
          simp only [pow_succ]
        _ ≤ (t:ℝ)^(j+3)+2*(t:ℝ)^2 := by
          have H := mul_le_mul_of_nonneg_left hst (by positivity : (0:ℝ) ≤ t+1)
          nlinarith
        _ ≤ 3*(t:ℝ)^(j+3) := by linarith
    have hmain : (2048*t*(ramsey (j+3) t)/Real.log t)*(Real.log (t:ℝ))^(j+2) ≤
        (2048*C)*(t:ℝ)^(j+3) := by
      calc
        _ = 2048*t*((ramsey (j+3) t : ℝ)*(Real.log (t:ℝ))^(j+1)) := by
          rw [show j+2 = (j+1)+1 from by omega, pow_succ]
          field_simp
        _ ≤ 2048*t*(C*(t:ℝ)^(j+2)) :=
          mul_le_mul_of_nonneg_left hCt (by positivity)
        _ = (2048*C)*(t:ℝ)^(j+3) := by
          rw [show j+3 = (j+2)+1 from by omega, pow_succ]; ring
    have H := mul_le_mul_of_nonneg_right (ramsey_recurrence j ht)
      (pow_nonneg hl.le (j+2))
    linear_combination H + hsmall + hmain

open Filter in
 theorem ramsey_upper {s : ℕ} (hs : 3 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (ramsey s t : ℝ) ≤ C*(t:ℝ)^(s-1)/(Real.log (t:ℝ))^(s-2) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨C,hC,hCb⟩ := ramsey_upper_scaled j
  refine ⟨C,hC,?_⟩
  have H : ∀ᶠ t : ℕ in atTop,
      (ramsey (3+j) t : ℝ) ≤ C*(t:ℝ)^(3+j-1)/(Real.log (t:ℝ))^(3+j-2) := by
    filter_upwards [hCb, eventually_ge_atTop (2:ℕ)] with t ht ht2
    have hl : 0 < Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    apply (le_div_iff₀ (pow_pos hl _)).mpr
    simpa [show 3+j = j+3 from by omega] using ht
  exact eventually_atTop.mp H

end SharpLogRamsey.Upper

end

end OAI
