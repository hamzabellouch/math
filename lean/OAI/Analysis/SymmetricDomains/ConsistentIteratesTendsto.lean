import Mathlib
import OAI.Analysis.SymmetricDomains.UniformCurveTaylor

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped NNReal

theorem finite_euler_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E → E) (S : Set E) {L : ℝ≥0} (hL : LipschitzOnWith L X S)
    (x y : ℕ → E) {N : ℕ} {h ε : ℝ} (hε : 0≤ε)
    (h0 : x 0=y 0) (hx : ∀ j<N, x j∈S) (hy : ∀ j<N, y j∈S)
    (hxe : ∀ j<N, ‖x (j+1)-x j-h • X (x j)‖≤ε*|h|)
    (hye : ∀ j<N, ‖y (j+1)-y j-h • X (y j)‖≤ε*|h|) :
    ‖x N-y N‖ ≤ (N:ℝ)*(2*ε*|h|)*Real.exp ((N:ℝ)*L*|h|) := by
  have hs (j : ℕ) (hj : j<N) :
      ‖x (j+1)-y (j+1)‖ ≤ (1+L*|h|)*‖x j-y j‖+2*ε*|h| := by
    have heq : x (j+1)-y (j+1) =
        ((x j-y j)+h • (X (x j)-X (y j)))+
        ((x (j+1)-x j-h • X (x j))-(y (j+1)-y j-h • X (y j))) := by
      rw [smul_sub]; abel
    have hl := hL.norm_sub_le (hx j hj) (hy j hj)
    rw [heq]
    calc
      _ ≤ (‖x j-y j‖+‖h • (X (x j)-X (y j))‖)+
          (‖x (j+1)-x j-h • X (x j)‖+‖y (j+1)-y j-h • X (y j)‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sub_le _ _))
      _ ≤ (‖x j-y j‖+|h| *(L*‖x j-y j‖))+(ε*|h|+ε*|h|) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (abs_nonneg _)))
          (add_le_add (hxe j hj) (hye j hj))
      _ = _ := by ring
  have hb : 0≤2*ε*|h| := by positivity
  have hc : 1≤1+(L:ℝ)*|h| := le_add_of_nonneg_right (mul_nonneg L.coe_nonneg (abs_nonneg _))
  have hf := finite_euler_error_bound (fun j => ‖x j-y j‖) hc hb (by simp [h0]) hs N le_rfl
  refine hf.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg N) hb))
  calc
    (1+(L:ℝ)*|h|)^N ≤ (Real.exp (L*|h|))^N := by
      exact pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp (L*|h|)) _
    _ = Real.exp ((N:ℝ)*L*|h|) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem consistent_iterates_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ → E → E) (X : E → E) (K : Set E) {L : ℝ≥0}
    (hL : LipschitzOnWith L X K)
    (hcons : ∀ ε : ℝ, 0<ε → ∀ᶠ h : ℝ in 𝓝 0, ∀ x∈K,
      ‖c h x-x-h • X x‖≤ε*|h|)
    (p : E) (α : ℝ → E) (t : ℝ) (hα0 : α 0=p)
    (hαK : ∀ s∈Icc (-|t|) |t|, α s∈K)
    (hαd : ∀ s∈Icc (-|t|) |t|, HasStrictDerivAt α (X (α s)) s)
    (hαv : ∀ s∈Icc (-|t|) |t|, ContinuousAt (fun s => X (α s)) s)
    (hit : ∀ N : ℕ, ∀ j≤N+1, ((c (t/(N+1)))^[j]) p∈K) :
    Tendsto (fun N : ℕ => ((c (t/(N+1)))^[N+1]) p) atTop (𝓝 (α t)) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  let C : ℝ := 2*|t| *Real.exp (L*|t|)
  have hC : 0≤C := by dsimp [C]; positivity
  let ε : ℝ := η/(C+1)
  have hε : 0<ε := div_pos hη (by linarith)
  have hεC : ε*C<η := by
    have he : ε*(C+1)=η := div_mul_cancel₀ η (by linarith)
    nlinarith
  have hdiv : Tendsto (fun N : ℕ => t/(N+1:ℕ)) atTop (𝓝 (0:ℝ)) :=
    (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
  have he := hdiv.eventually (hcons ε hε)
  have hy := hdiv.eventually (uniform_curve_taylor α (fun s => X (α s))
    (Icc (-|t|) |t|) isCompact_Icc hαv hαd hε)
  have hev : ∀ᶠ N : ℕ in atTop, dist (((c (t/(N+1)))^[N+1]) p) (α t)<η := by
    filter_upwards [he,hy] with N hN hNy
    have hNr : (0:ℝ)<(N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
    have hNe : ((N+1:ℕ):ℝ)≠0 := ne_of_gt hNr
    let h : ℝ := t/(N+1:ℕ)
    let x : ℕ → E := fun j => ((c h)^[j]) p
    let y : ℕ → E := fun j => α ((j:ℝ)*h)
    have hsj {j : ℕ} (hj : j≤N+1) : (j:ℝ)*h ∈ Icc (-|t|) |t| := by
      have hj0 : (0:ℝ)≤j := Nat.cast_nonneg j
      have hjn : (j:ℝ)≤(N+1:ℕ) := Nat.cast_le.mpr hj
      have ha : |(j:ℝ)*h|≤|t| := by
        rw [abs_mul,abs_of_nonneg hj0,show |h|=|t|/((N+1:ℕ):ℝ) by dsimp [h]; rw [abs_div,abs_of_pos hNr]]
        calc
          _ ≤ ((N+1:ℕ):ℝ)*(|t|/((N+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_right hjn (div_nonneg (abs_nonneg t) hNr.le)
          _ = |t| := mul_div_cancel₀ _ hNe
      exact abs_le.mp ha
    have hxj (j : ℕ) (hj : j<N+1) : x j∈K := by
      simpa only [x,h,Nat.cast_add,Nat.cast_one] using hit N j hj.le
    have hyj (j : ℕ) (hj : j<N+1) : y j∈K := hαK _ (hsj hj.le)
    have hxe (j : ℕ) (hj : j<N+1) : ‖x (j+1)-x j-h • X (x j)‖≤ε*|h| := by
      have he' := hN (x j) (hxj j hj)
      simpa only [x,h,Function.iterate_succ_apply'] using he'
    have hye (j : ℕ) (hj : j<N+1) : ‖y (j+1)-y j-h • X (y j)‖≤ε*|h| := by
      have he' := hNy ((j:ℝ)*h) (hsj hj.le)
      have heq : ((j+1:ℕ):ℝ)*h=(j:ℝ)*h+h := by rw [Nat.cast_add,Nat.cast_one]; ring
      simpa only [y,heq] using he'
    have hv := finite_euler_comparison X K hL x y hε.le (by simp [x,y,hα0]) hxj hyj hxe hye
    have hyend : y (N+1)=α t := by dsimp [y,h]; rw [mul_div_cancel₀ _ hNe]
    have hend : ((N+1:ℕ):ℝ)*(2*ε*|h|)*Real.exp (((N+1:ℕ):ℝ)*L*|h|)=ε*C := by
      have hh : |h|=|t|/((N+1:ℕ):ℝ) := by dsimp [h]; rw [abs_div,abs_of_pos hNr]
      rw [hh]
      have hq : ((N+1:ℕ):ℝ)*(L:ℝ)*(|t|/((N+1:ℕ):ℝ))=L*|t| := by field_simp
      rw [hq]
      dsimp [C]
      field_simp
    rw [hyend,hend] at hv
    simpa only [dist_eq_norm,x,h,Nat.cast_add,Nat.cast_one] using hv.trans_lt hεC
  exact Filter.eventually_atTop.mp hev

end Release061

end

end OAI
