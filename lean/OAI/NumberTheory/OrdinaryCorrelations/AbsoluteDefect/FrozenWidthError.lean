import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpWindowIocAdd

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinarySharpWindow
open Finset MeasureTheory
lemma frozen_width_error {X D c δ n : ℝ} (hX : 0 < X) (hD : 0 ≤ D)
    (hDX : D ≤ X) (hc : 1 ≤ c) (hδ : 0 ≤ δ) (hn0 : c*X ≤ n)
    (hn1 : n ≤ (c+δ)*X) (hn2 : n ≤ 2*X) :
    |D-n*(Real.exp ((D/c)/X)-1)| ≤ δ*D+2*D^2/X := by
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hnp : 0 < n := (mul_pos hcp hX).trans_le hn0
  let H := (D/c)/X
  have hH : 0 ≤ H := div_nonneg (div_nonneg hD hcp.le) hX.le
  have hHbound : H ≤ D/X := div_le_div_of_nonneg_right (div_le_self hD hc) hX.le
  have hHone : H ≤ 1 := hHbound.trans ((div_le_one hX).mpr hDX)
  have hCH : c*X*H=D := by dsimp [H]; field_simp
  have hXH : X*H=D/c := by dsimp [H]; field_simp
  have hlinlow : D ≤ n*H := by nlinarith only [mul_le_mul_of_nonneg_right hn0 hH,hCH]
  have hlinhi : n*H-D ≤ δ*D := by
    have hh := mul_le_mul_of_nonneg_right hn1 hH
    have hdc := div_le_self hD hc
    have hdd := mul_le_mul_of_nonneg_left hdc hδ
    have he : (c+δ)*X*H=c*X*H+δ*(X*H) := by ring
    rw [he,hCH,hXH] at hh
    linarith only [hh,hdd]
  have hexp := Real.abs_exp_sub_one_sub_id_le (show |H| ≤ 1 by rwa [abs_of_nonneg hH])
  have hsq : H^2 ≤ (D/X)^2 := sq_le_sq₀ hH (div_nonneg hD hX.le) |>.mpr hHbound
  have hquad : n*H^2 ≤ 2*D^2/X := by
    have hh := mul_le_mul hn2 hsq (sq_nonneg H) (by positivity : 0 ≤ 2*X)
    have he : 2*X*(D/X)^2=2*D^2/X := by field_simp
    rwa [he] at hh
  calc
    _ = |(D-n*H)-n*(Real.exp H-1-H)| := by dsimp [H]; congr 1; ring
    _ ≤ |D-n*H|+|n*(Real.exp H-1-H)| := abs_sub _ _
    _ = (n*H-D)+n*|Real.exp H-1-H| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hlinlow),abs_mul,abs_of_pos hnp]
      ring
    _ ≤ δ*D+2*D^2/X := by
      have hh := mul_le_mul_of_nonneg_left hexp hnp.le
      linarith only [hlinhi,hquad,hh]

def bandCut (X k j : ℕ) : ℕ := X+X*j/k
lemma bandCut_zero (X k : ℕ) : bandCut X k 0=X := by simp [bandCut]
lemma bandCut_end (X : ℕ) {k : ℕ} (hk : 0 < k) : bandCut X k k=2*X := by
  simp [bandCut,Nat.mul_div_cancel _ hk, two_mul]
lemma bandCut_mono (X k : ℕ) : Monotone (bandCut X k) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_left X hij)) X
lemma bandCut_lower (X k j : ℕ) : X ≤ bandCut X k j := by simp [bandCut]
lemma bandCut_upper (X : ℕ) {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) : bandCut X k j ≤ 2*X := by
  simpa only [bandCut_end X hk] using bandCut_mono X k hj
lemma bandCut_real_upper (X j : ℕ) {k : ℕ} (hk : 0 < k) :
    (bandCut X k j:ℝ) ≤ (1+(j:ℝ)/k)*X := by
  have hh : (k:ℝ)*(X*j/k:ℕ) ≤ (X:ℝ)*j := by exact_mod_cast Nat.mul_div_le (X*j) k
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hd : (X*j/k:ℕ) ≤ (X:ℝ)*j/k := (le_div_iff₀ hkr).mpr (by nlinarith only [hh])
  dsimp [bandCut]
  push_cast
  calc
    _ ≤ (X:ℝ)+(X:ℝ)*j/k := add_le_add le_rfl hd
    _ = _ := by ring
lemma bandCut_real_lower {X k j n : ℕ} (hk : 0 < k) (hn : bandCut X k j < n) :
    (1+(j:ℝ)/k)*X ≤ (n:ℝ) := by
  have hh : (X:ℝ)*j < (k:ℝ)*((X*j/k:ℕ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ (X*j) hk
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hd : (X:ℝ)*j/k < ((X*j/k:ℕ):ℝ)+1 := (div_lt_iff₀ hkr).mpr (by nlinarith only [hh])
  have hnn : (X:ℝ)+(X*j/k:ℕ)+1 ≤ (n:ℝ) := by exact_mod_cast hn
  calc
    _ = (X:ℝ)+(X:ℝ)*j/k := by ring
    _ ≤ (X:ℝ)+(X*j/k:ℕ)+1 := by linarith only [hd]
    _ ≤ (n:ℝ) := hnn

lemma sharpWindow_partition (a : ℕ→ℂ) (u : ℕ→ℝ) (H x : ℝ) (X : ℕ) {k : ℕ} (hk : 0 < k) :
    sharpWindow (Ioc X (2*X)) a u H x =
      ∑j∈range k,sharpWindow (Ioc (bandCut X k j) (bandCut X k (j+1))) a u H x := by
  have he (j : ℕ) : sharpWindow (Ioc (bandCut X k j) (bandCut X k (j+1))) a u H x =
      sharpWindow (Ioc X (bandCut X k (j+1))) a u H x-
      sharpWindow (Ioc X (bandCut X k j)) a u H x := by
    have hh := sharpWindow_Ioc_add a u H x (bandCut_lower X k j)
      (bandCut_mono X k (Nat.le_succ j))
    rw [← hh,add_sub_cancel_left]
  simp_rw [he]
  rw [sum_range_sub (fun j=>sharpWindow (Ioc X (bandCut X k j)) a u H x) k,bandCut_end X hk,bandCut_zero]
  simp [sharpWindow]

lemma sharpWindow_partition_l1 (a : ℕ→ℂ) (u : ℕ→ℝ) (H : ℝ) (X : ℕ) {k : ℕ} (hk : 0 < k) :
    (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) a u H x‖) ≤
      ∑j∈range k,∫x : ℝ,‖sharpWindow (Ioc (bandCut X k j) (bandCut X k (j+1))) a u H x‖ := by
  rw [← integral_finsetSum (range k) (fun j hj=>(sharpWindow_integrable _ a u H).norm)]
  apply integral_mono (sharpWindow_integrable _ a u H).norm
    (integrable_finsetSum (range k) (fun j hj=>(sharpWindow_integrable _ a u H).norm))
  intro x
  dsimp only
  rw [sharpWindow_partition a u H x X hk]
  exact norm_sum_le _ _

lemma band_card_sum (X : ℕ) {k : ℕ} (hk : 0 < k) :
    (∑j∈range k,((Finset.Ioc (bandCut X k j) (bandCut X k (j+1))).card:ℝ))=X := by
  have he (j : ℕ) : ((Finset.Ioc (bandCut X k j) (bandCut X k (j+1))).card:ℝ)=
      (bandCut X k (j+1):ℝ)-(bandCut X k j:ℝ) := by
    rw [Nat.card_Ioc,Nat.cast_sub (bandCut_mono X k (Nat.le_succ j))]
  simp_rw [he]
  rw [sum_range_sub (fun j=>(bandCut X k j:ℝ)) k,bandCut_end X hk,bandCut_zero]
  push_cast
  ring

end OrdinarySharpWindow

end

end OAI
