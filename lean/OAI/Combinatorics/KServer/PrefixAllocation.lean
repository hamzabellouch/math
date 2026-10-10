import Mathlib
import OAI.Combinatorics.KServer.AllocationBudget

namespace OAI

/- Persistent heavy-slot size tracking filters tangents before adaptive refresh. -/


noncomputable section
open scoped BigOperators
open Set Finset
namespace KServer.KeySizeTracking

def tangent (u s : ℝ) : ℝ := u - (1 + Real.log u) * s

def entropy (u s : ℝ) : ℝ := s * Real.log (s / u) - s + u

lemma tangent_credit {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    tangent u s - tangent s s = entropy u s := by
  rw [entropy, Real.log_div hs.ne' hu.ne']
  unfold tangent
  ring

lemma lower_ratio {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (x - 1)^2 / 2 ≤ x * Real.log x - x + 1 := by
  let f : ℝ → ℝ := fun y => (y-1)^2/2 - (y*Real.log y-y+1)
  have hd (y : ℝ) (hy : 0 < y) : HasDerivAt f (y-1-Real.log y) y := by
    have h := (((hasDerivAt_id y).sub_const 1).pow 2).div_const 2
    have h' := (((hasDerivAt_id y).mul (Real.hasDerivAt_log hy.ne')).sub
      (hasDerivAt_id y)).add_const 1
    convert h.sub h' using 1 <;> first | rfl | (norm_num [id_eq]; field_simp [hy.ne']; ring)
  have hm : MonotoneOn f (Icc x 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x 1)
    · intro y hy
      exact (hd y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (hx.trans_le (interior_subset hy).1)).hasDerivWithinAt
    · intro y hy
      have h := Real.log_le_sub_one_of_pos (hx.trans_le (interior_subset hy).1)
      linarith
  have h := hm ⟨le_rfl,hx1⟩ ⟨hx1,le_rfl⟩ hx1
  dsimp [f] at h
  norm_num at h
  linarith

lemma upper_ratio {x : ℝ} (hx : 1 ≤ x) :
    (x - 1)^2 / (2*x) ≤ x * Real.log x - x + 1 := by
  let f : ℝ → ℝ := fun y => y*Real.log y-y+1 - (y-1)^2/(2*y)
  have hd (y : ℝ) (hy : 0 < y) :
      HasDerivAt f (Real.log y - (1-y⁻¹^2)/2) y := by
    have h := (((hasDerivAt_id y).mul (Real.hasDerivAt_log hy.ne')).sub
      (hasDerivAt_id y)).add_const 1
    have h' := (((hasDerivAt_id y).sub_const 1).pow 2).div
      ((hasDerivAt_id y).const_mul 2) (by positivity : 2*y ≠ 0)
    convert h.sub h' using 1 <;> first | rfl | (norm_num [id_eq]; field_simp [hy.ne']; ring)
  have hm : MonotoneOn f (Icc 1 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
    · intro y hy
      exact (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (by linarith [(interior_subset hy).1])).hasDerivWithinAt
    · intro y hy
      have hp : 0 < y := by linarith [(interior_subset hy).1]
      have h := Real.one_sub_inv_le_log_of_pos hp
      nlinarith [sq_nonneg (1-y⁻¹)]
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  dsimp [f] at h
  norm_num at h
  linarith

lemma entropy_quadratic {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    (s-u)^2 / (2*max s u) ≤ entropy u s := by
  have hx : 0 < s/u := div_pos hs hu
  have he : entropy u s = u*((s/u)*Real.log (s/u)-s/u+1) := by
    unfold entropy
    field_simp
  rw [he]
  rcases le_total s u with hsu | hus
  · rw [max_eq_right hsu]
    have h := mul_le_mul_of_nonneg_left
      (lower_ratio hx ((div_le_one hu).mpr hsu)) hu.le
    convert h using 1; first | rfl | field_simp
  · rw [max_eq_left hus]
    have h := mul_le_mul_of_nonneg_left
      (upper_ratio ((one_le_div hu).mpr hus)) hu.le
    convert h using 1; first | rfl | field_simp

lemma relative_credit {u s : ℝ} (hu : 0 < u) (hs : 0 < s)
    (hfail : s < (5/6:ℝ)*u ∨ (6/5:ℝ)*u < s) :
    (s+u)/144 ≤ tangent u s-tangent s s := by
  rw [tangent_credit hu hs]
  have hq := entropy_quadratic hu hs
  have hm : 0 < max s u := lt_of_lt_of_le hs (le_max_left _ _)
  have hgap : (max s u / 6)^2 ≤ (s-u)^2 := by
    rcases hfail with h | h
    · have hsu : s ≤ u := by linarith
      rw [max_eq_right hsu]
      nlinarith
    · have hus : u ≤ s := by linarith
      rw [max_eq_left hus]
      nlinarith
  have hsum : s+u ≤ 2*max s u := by linarith [le_max_left s u,le_max_right s u]
  have hh : (s+u)/144 ≤ (s-u)^2/(2*max s u) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsum hm.le]
  exact hh.trans hq


variable {Ω : Type} [Fintype Ω]

def avg (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω*f ω

lemma avg_add (w f g : Ω → ℝ) : avg w (fun ω => f ω+g ω)=avg w f+avg w g := by
  simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (w f g : Ω → ℝ) : avg w (fun ω => f ω-g ω)=avg w f-avg w g := by
  simp [avg,mul_sub,sum_sub_distrib]
lemma avg_mul (w f : Ω → ℝ) (c : ℝ) : avg w (fun ω => c*f ω)=c*avg w f := by
  simp only [avg,mul_sum,mul_left_comm (w _) c]
lemma avg_sum (w : Ω → ℝ) {ι : Type} [Fintype ι] (f : ι → Ω → ℝ) :
    avg w (fun ω => ∑ i, f i ω)=∑ i, avg w (f i) := by
  simp only [avg,mul_sum]; rw [sum_comm]
lemma avg_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    avg w f ≤ avg w g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)
lemma avg_const (w : Ω → ℝ) (hw : ∑ ω, w ω=1) (c : ℝ) : avg w (fun _ => c)=c := by
  simp [avg,←sum_mul,hw]

def Adapted (H : Ω → ℕ) (f : Ω → ℝ) : Prop := ∀ ω ω', H ω=H ω' → f ω=f ω'

lemma fiber_weighted_zero (H : Ω → ℕ) (f g : Ω → ℝ)
    (hf : Adapted H f) (hg : ∀ h, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω=0) :
    ∑ ω, f ω*g ω=0 := by
  classical
  let c : ℕ → ℝ := fun h => if hh : ∃ ω, H ω=h then f hh.choose else 0
  have hc : ∀ ω, f ω=c (H ω) := by
    intro ω
    dsimp [c]
    rw [dite_eq_left ⟨ω,rfl⟩]
    exact hf ω _ (Exists.choose_spec (show ∃ ω', H ω'=H ω from ⟨ω,rfl⟩)).symm
  have hs : (∑ ω, f ω*g ω) =
      ∑ h ∈ Finset.univ.image H, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), f ω*g ω := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (by intro ω _; exact Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩) _
  rw [hs]
  apply sum_eq_zero
  intro h _
  calc _ = c h*(∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro ω hω
        rw [hc ω,(Finset.mem_filter.mp hω).2]
       _ = 0 := by rw [hg,mul_zero]

/-- Old and new membership counts shifted by one, with literal finite-fiber
conditioning. There is no policy-existence or budget assumption in this data. -/
structure FilteredSizes (w : Ω → ℝ) (K : ℝ) where
  history : ℕ → Ω → ℕ
  refines : ∀ t ω ω', history (t+1) ω=history (t+1) ω' → history t ω=history t ω'
  s : ℕ → Ω → ℝ
  before : ℕ → Ω → ℝ
  range : ∀ t ω, s t ω ∈ Set.Icc 1 K
  before_range : ∀ t ω, before t ω ∈ Set.Icc 1 K
  adapted : ∀ t, Adapted (history t) (s t)
  filtering : ∀ t h, ∑ ω ∈ Finset.univ.filter (fun ω => history t ω=h),
    w ω*(before (t+1) ω-s t ω)=0

def refresh (s u : ℝ) : Prop := s < (5/6:ℝ)*u ∨ (6/5:ℝ)*u < s
instance : DecidableRel refresh := Classical.decRel _

def held (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, ω => s 0 ω
  | t+1, ω => if refresh (s (t+1) ω) (held s t ω) then s (t+1) ω else held s t ω

omit [Fintype Ω] in
lemma held_range {s : ℕ → Ω → ℝ} {K : ℝ} (hs : ∀ t ω, s t ω ∈ Icc 1 K) :
    ∀ t ω, held s t ω ∈ Icc 1 K := by
  intro t
  induction t with
  | zero => exact hs 0
  | succ t ih => intro ω; dsimp [held]; split_ifs <;> [exact hs _ _; exact ih ω]

lemma held_adapted {w : Ω → ℝ} {K : ℝ} (R : FilteredSizes w K) :
    ∀ t, Adapted (R.history t) (held R.s t) := by
  intro t
  induction t with
  | zero => exact R.adapted 0
  | succ t ih =>
    intro ω ω' hh
    have hprev := ih ω ω' (R.refines t ω ω' hh)
    have hnow := R.adapted (t+1) ω ω' hh
    simp only [held,hnow,hprev]

omit [Fintype Ω] in
lemma held_accurate {s : ℕ → Ω → ℝ} (hs : ∀ t ω, 0 ≤ s t ω) (t : ℕ) (ω : Ω) :
    (5/6:ℝ)*held s t ω ≤ s t ω ∧ s t ω ≤ (6/5:ℝ)*held s t ω := by
  cases t with
  | zero => dsimp [held]; constructor <;> nlinarith [hs 0 ω]
  | succ t =>
    dsimp [held]
    split_ifs with h
    · constructor <;> nlinarith [hs (t+1) ω]
    · simp only [refresh,not_or,not_lt] at h
      exact h

lemma slope_bound {K u : ℝ} (hu : u ∈ Icc 1 K) :
    |-(1+Real.log u)| ≤ 1+Real.log K := by
  have hp : 0 < u := by linarith [hu.1]
  have hl := Real.log_nonneg hu.1
  rw [abs_neg,abs_of_nonneg (by linarith : 0 ≤ 1+Real.log u)]
  linarith [Real.log_le_log hp hu.2]

lemma tangent_bound {K u s : ℝ} (hu : u ∈ Icc 1 K) (hs : s ∈ Icc 1 K) :
    |tangent u s| ≤ K*(1+(1+Real.log K)) := by
  have hK : 1 ≤ K := hu.1.trans hu.2
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hL : 0 ≤ 1+Real.log K := by linarith [Real.log_nonneg hK]
  have h := slope_bound hu
  rw [abs_neg] at h
  calc |tangent u s| ≤ |u|+|(1+Real.log u)*s| := by simpa [tangent] using abs_sub_le u 0 ((1+Real.log u)*s)
       _ = u+|1+Real.log u| * s := by rw [abs_of_nonneg hu0,abs_mul,abs_of_nonneg hs0]
       _ ≤ K+(1+Real.log K)*K := add_le_add hu.2 (mul_le_mul h hs.2 hs0 hL)
       _ = _ := by ring

def refreshCost (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if refresh (s (t+1) ω) (held s t ω) then held s t ω+held s (t+1) ω else 0

omit [Fintype Ω] in
lemma refresh_cost_step {s : ℕ → Ω → ℝ} {K : ℝ}
    (hs : ∀ t ω, s t ω ∈ Icc 1 K) (t : ℕ) (ω : Ω) :
    refreshCost s t ω /144 ≤
      tangent (held s t ω) (s t ω)-tangent (held s (t+1) ω) (s (t+1) ω) +
      (-(1+Real.log (held s t ω)))*(s (t+1) ω-s t ω) := by
  have hp : 0 < held s t ω := by linarith [(held_range hs t ω).1]
  have hp' : 0 < s (t+1) ω := by linarith [(hs (t+1) ω).1]
  have he : tangent (held s t ω) (s t ω)-tangent (held s (t+1) ω) (s (t+1) ω) +
      (-(1+Real.log (held s t ω)))*(s (t+1) ω-s t ω) =
      tangent (held s t ω) (s (t+1) ω)-tangent (held s (t+1) ω) (s (t+1) ω) := by
    unfold tangent; ring
  rw [he]
  dsimp [refreshCost,held]
  split_ifs with h
  · simpa only [add_comm] using relative_credit hp hp' h
  · simp

lemma filtering_zero {w : Ω → ℝ} {K : ℝ} (R : FilteredSizes w K) (t : ℕ) :
    avg w (fun ω => (-(1+Real.log (held R.s t ω)))*(R.before (t+1) ω-R.s t ω))=0 := by
  unfold avg
  simp_rw [mul_left_comm (w _) (-(1+Real.log (held R.s t _)))]
  apply fiber_weighted_zero (R.history t) _ _ _ (R.filtering t)
  intro ω ω' hh
  dsimp only
  rw [held_adapted R t ω ω' hh]

lemma expected_refresh_step {w : Ω → ℝ} {K : ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (R : FilteredSizes w K) (t : ℕ) :
    avg w (refreshCost R.s t)/144 ≤
      avg w (fun ω => tangent (held R.s t ω) (R.s t ω))-
      avg w (fun ω => tangent (held R.s (t+1) ω) (R.s (t+1) ω))+
      (1+Real.log K)*avg w (fun ω => |R.s (t+1) ω-R.before (t+1) ω|) := by
  have hs := avg_mono hw (refresh_cost_step R.range t)
  have he : avg w (fun ω => refreshCost R.s t ω/144)=avg w (refreshCost R.s t)/144 := by
    simp only [avg,←mul_div_assoc,Finset.sum_div]
  rw [he] at hs
  have hsplit : ∀ ω,
      (-(1+Real.log (held R.s t ω)))*(R.s (t+1) ω-R.s t ω) =
      (-(1+Real.log (held R.s t ω)))*(R.before (t+1) ω-R.s t ω)+
      (-(1+Real.log (held R.s t ω)))*(R.s (t+1) ω-R.before (t+1) ω) := by intro ω; ring
  simp_rw [hsplit] at hs
  rw [avg_add,avg_sub,avg_add,filtering_zero,zero_add] at hs
  apply hs.trans
  apply add_le_add le_rfl
  rw [←avg_mul]
  apply avg_mono hw
  intro ω
  calc _ ≤ |(-(1+Real.log (held R.s t ω)))*(R.s (t+1) ω-R.before (t+1) ω)| := le_abs_self _
       _ ≤ _ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (slope_bound (held_range R.range t ω)) (abs_nonneg _)

/-- Size-refresh budget, before substituting the mapped-member
transport bound. Crucially the constant is independent of the horizon. -/
theorem size_refresh_budget {w : Ω → ℝ} {K : ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω=1) (R : FilteredSizes w K) (N : ℕ) :
    ∑ t ∈ range N, avg w (refreshCost R.s t) ≤
      144*(1+Real.log K)*(∑ t ∈ range N, avg w (fun ω => |R.s (t+1) ω-R.before (t+1) ω|))+
      288*K*(1+(1+Real.log K)) := by
  let V : ℕ → ℝ := fun t => avg w (fun ω => tangent (held R.s t ω) (R.s t ω))
  let B : ℝ := K*(1+(1+Real.log K))
  have hV t : -B ≤ V t ∧ V t ≤ B := by
    have hb ω := abs_le.mp (tangent_bound (held_range R.range t ω) (R.range t ω))
    constructor
    · have h := avg_mono hw (fun ω => (hb ω).1)
      simpa only [avg_const w hw1 (-(K*(1+(1+Real.log K))))] using h
    · have h := avg_mono hw (fun ω => (hb ω).2)
      simpa only [avg_const w hw1 (K*(1+(1+Real.log K)))] using h
  have hsum := sum_le_sum (s := range N) (fun t _ => expected_refresh_step hw R t)
  change (∑ t ∈ range N, avg w (refreshCost R.s t)/144) ≤
    ∑ t ∈ range N, (V t-V (t+1)+(1+Real.log K)*avg w (fun ω => |R.s (t+1) ω-R.before (t+1) ω|)) at hsum
  rw [←sum_div,sum_add_distrib,Finset.sum_range_sub',←mul_sum] at hsum
  dsimp [B] at hV
  nlinarith [(hV 0).2,(hV N).1]

end KServer.KeySizeTracking

end


/-! Persistent heavy-slot size tracking on the actual finite observation
experiment. Raw counts can change with both the hidden trajectory and the
adapted partition. No martingale identity is postulated. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PosteriorSizes
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω] {w:Ω→ℝ}

lemma bounded (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) (H:Ω→ℕ)
    {f:Ω→ℝ} {K:ℝ} (hf:∀ ω,f ω∈Set.Icc 0 K) (ω:Ω):
    posterior w H f ω∈Set.Icc 0 K:=by
  refine ⟨posterior_nonneg hw H (fun ρ=>(hf ρ).1) ω,?_⟩
  have h:=posterior_mono_fiber hw (H:=H) (g:=fun _=>K) ω (fun ρ _=>(hf ρ).2)
  rw [posterior_fiber_const ω (fun _ _=>rfl) (HierarchyCounts.positive_mass hw H ω (hwpos ω)).ne'] at h
  exact h

def process (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) {K:ℝ}
    (H:ℕ→Ω→ℕ) (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (N:ℕ→Ω→ℝ) (hN:∀ t ω,N t ω∈Set.Icc 0 K):KeySizeTracking.FilteredSizes w (K+1) where
  history:=H
  refines:=hr
  s t ω:=1+posterior w (H t) (N t) ω
  before t ω:=1+posterior w (H t) (N (t-1)) ω
  range:=by intro t ω; have h:=bounded hw hwpos (H t) (hN t) ω; constructor <;> linarith [h.1,h.2]
  before_range:=by intro t ω; have h:=bounded hw hwpos (H t) (hN (t-1)) ω; constructor <;> linarith [h.1,h.2]
  adapted:=by
    intro t ω ρ he
    exact congrArg (1+·) (posterior_adapted w (H t) (N t) ω ρ he)
  filtering:=by
    intro t h
    simp only [Nat.add_sub_cancel,add_sub_add_left_eq_sub]
    exact filtered_fiber hw (H t) (H (t+1)) (hr t) (N t) h

lemma process_drift (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) {K:ℝ}
    (H:ℕ→Ω→ℕ) (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (N:ℕ→Ω→ℝ) (hN:∀ t ω,N t ω∈Set.Icc 0 K) (t:ℕ):
    avg w (fun ω=>|(process hw hwpos H hr N hN).s (t+1) ω-
      (process hw hwpos H hr N hN).before (t+1) ω|)≤
        avg w (fun ω=>|N (t+1) ω-N t ω|):=by
  simp only [process,Nat.add_sub_cancel,add_sub_add_left_eq_sub]
  exact posterior_drift hw (H (t+1)) (N (t+1)) (N t)

lemma refresh_budget (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) (hw1:∑ ω,w ω=1)
    {K:ℝ} (hK:0≤K) (H:ℕ→Ω→ℕ)
    (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (N:ℕ→Ω→ℝ) (hN:∀ t ω,N t ω∈Set.Icc 0 K) (T:ℕ):
    (∑ t∈range T,avg w (KeySizeTracking.refreshCost (process hw hwpos H hr N hN).s t)) ≤
      144*(1+Real.log (K+1))*(∑ t∈range T,avg w (fun ω=>|N (t+1) ω-N t ω|))+
        288*(K+1)*(1+(1+Real.log (K+1))):=by
  have h:=KeySizeTracking.size_refresh_budget hw hw1
    (process hw hwpos H hr N hN) T
  have hm:=sum_le_sum (s:=range T) (fun t _=>process_drift hw hwpos H hr N hN t)
  have hp:0≤144*(1+Real.log (K+1)):=by have :=Real.log_nonneg (by linarith : 1≤K+1); positivity
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hm hp) (le_refl _))

end KServer.PosteriorSizes

end


/-! Literal children and geometric edge weights of the retained complete
prefix tree. These identify the numbered rounding tree without deleting empty
words or changing its allocated coordinates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

abbrev Child (v:Vertex A L):= {u:Vertex A L // u≠root A L ∧ parent A L u=v}

omit [Fintype A] in
lemma depth_zero_iff (v:Vertex A L):v.1.val=0 ↔ v=root A L:=by
  constructor
  · rintro h
    rcases v with ⟨j,f⟩
    have hj:j=0:=Fin.ext h
    subst j
    congr
    exact funext (fun i=>Fin.elim0 i)
  · rintro rfl; rfl

omit [Fintype A] in
lemma parent_succ {d:ℕ} (hd:d+1<L+1) (f:Fin (d+1)→A):
    parent A L ⟨⟨d+1,hd⟩,f⟩=⟨⟨d,by omega⟩,Fin.init f⟩:=by
  simp only [parent,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceDIte]
  rfl

omit [Fintype A] in
lemma child_depth {v:Vertex A L} (u:Child A L v):u.val.1.val=v.1.val+1:=by
  have hp:0<u.val.1.val:=Nat.pos_of_ne_zero ((depth_zero_iff A L _).not.mpr u.property.1)
  have he:=congrArg (fun x:Vertex A L=>x.1.val) u.property.2
  simp only [parent,dite_eq_right (by omega : u.val.1.val≠0)] at he
  omega

omit [Fintype A] in
lemma child_last_lt {v:Vertex A L} (u:Child A L v):u.val.1.val-1<u.val.1.val:=by
  have :=child_depth A L u
  omega

def extend (v:Vertex A L) (h:v.1.val<L) (a:A):Vertex A L:=
  ⟨⟨v.1.val+1,by omega⟩,Fin.snoc v.2 a⟩

omit [Fintype A] in
lemma parent_extend (v:Vertex A L) (h:v.1.val<L) (a:A):
    parent A L (extend A L v h a)=v:=by
  rw [extend,parent_succ]
  simp only [Fin.init_snoc]

omit [Fintype A] in
lemma extend_ne_root (v:Vertex A L) (h:v.1.val<L) (a:A):
    extend A L v h a≠root A L:=by
  intro he
  have he':=(depth_zero_iff A L _).mpr he
  dsimp [extend] at he'
  omega

def childEquiv (v:Vertex A L) (h:v.1.val<L):A≃Child A L v where
  toFun a:=⟨extend A L v h a,extend_ne_root A L v h a,parent_extend A L v h a⟩
  invFun u:=u.val.2 ⟨u.val.1.val-1,child_last_lt A L u⟩
  left_inv a:=by
    simp only [extend,Nat.add_sub_cancel]
    exact Fin.snoc_last _ _
  right_inv u:=by
    apply Subtype.ext
    rcases v with ⟨⟨d,hd⟩,f⟩
    rcases u with ⟨⟨⟨e,he⟩,g⟩,hn,hp⟩
    have hdeg:e=d+1:=child_depth A L ⟨_,hn,hp⟩
    subst e
    rw [parent_succ] at hp
    have hf:Fin.init g=f:=by cases hp; rfl
    dsimp only [extend,Nat.add_sub_cancel]
    change (⟨⟨d+1,he⟩,Fin.snoc f (g (Fin.last d))⟩:Vertex A L) = _
    rw [←hf]
    have hg:Fin.snoc (Fin.init g) (g (Fin.last d))=g:=Fin.snoc_init_self g
    exact congrArg (fun f:Fin (d+1)→A=>(⟨⟨d+1,he⟩,f⟩:Vertex A L)) hg

omit [Fintype A] in
lemma no_child (v:Vertex A L) (h:v.1.val=L):IsEmpty (Child A L v):=by
  refine ⟨fun u=>?_⟩
  have hd:=child_depth A L u
  have hu:=u.val.1.isLt
  omega

def numberedChildEquiv (v:Fin (Fintype.card (Vertex A L))):
    (tree A L).Child v ≃ Child A L (numbering A L v) where
  toFun u:=⟨numbering A L u.val,by
    constructor
    · intro he
      apply u.property.1
      apply (numbering A L).injective
      rw [he,numbering_zero]
    · have he:=congrArg (numbering A L) u.property.2
      simpa only [tree,OrderIso.apply_symm_apply] using he⟩
  invFun u:=⟨(numbering A L).symm u.val,by
    constructor
    · intro he
      apply u.property.1
      have hh:=congrArg (numbering A L) he
      simpa only [OrderIso.apply_symm_apply,numbering_zero] using hh
    · change (numbering A L).symm (parent A L (numbering A L ((numbering A L).symm u.val)))=v
      rw [OrderIso.apply_symm_apply,u.property.2,OrderIso.symm_apply_apply]⟩
  left_inv u:=by apply Subtype.ext; exact OrderIso.symm_apply_apply _ _
  right_inv u:=by apply Subtype.ext; exact OrderIso.apply_symm_apply _ _

lemma children_sum (v:Fin (Fintype.card (Vertex A L))) (f:Vertex A L→ℝ)
    (h:(numbering A L v).1.val<L):
    (∑ u:(tree A L).Child v,f (numbering A L u.val))=
      ∑ a:A,f (extend A L (numbering A L v) h a):=by
  let e: A ≃ (tree A L).Child v :=
    (childEquiv A L (numbering A L v) h).trans (numberedChildEquiv A L v).symm
  symm
  exact Fintype.sum_equiv e _ _ (fun a=>by
    change f (extend A L (numbering A L v) h a) =
      f (numbering A L ((numbering A L).symm (extend A L (numbering A L v) h a)))
    rw [OrderIso.apply_symm_apply])

lemma children_sum_leaf (v:Fin (Fintype.card (Vertex A L))) (f:Vertex A L→ℝ)
    (h:(numbering A L v).1.val=L):
    (∑ u:(tree A L).Child v,f (numbering A L u.val))=0:=by
  let: IsEmpty (Child A L (numbering A L v)):=no_child A L _ h
  let:IsEmpty ((tree A L).Child v):=Function.isEmpty (numberedChildEquiv A L v)
  exact sum_of_isEmpty _

def weight (R τ:ℝ) (v:Fin (Fintype.card (Vertex A L))):ℝ:=
  R/τ^(numbering A L v).1.val

lemma weight_nonneg {R τ:ℝ} (hR:0≤R) (hτ:0≤τ) (v:Fin (Fintype.card (Vertex A L))):
    0≤weight A L R τ v:=div_nonneg hR (pow_nonneg hτ _)

lemma parent_weight {R τ:ℝ} (hτ:τ≠0) (v:Fin (Fintype.card (Vertex A L))) (hv:v≠0):
    weight A L R τ ((tree A L).parent v)=τ*weight A L R τ v:=by
  let hu:Child A L (numbering A L ((tree A L).parent v)):=
    numberedChildEquiv A L _ ⟨v,hv,rfl⟩
  have he: (numbering A L v).1.val=(numbering A L ((tree A L).parent v)).1.val+1:=
    by simpa only [hu,numberedChildEquiv,Equiv.coe_fn_mk] using child_depth A L hu
  unfold weight
  rw [he,pow_succ]
  field_simp

end KServer.PrefixTree

end


/-! Quotas and parks on the actual numbered complete-prefix tree, with their
posterior support witnesses. Rounding.Tree and TreeRounding.Tree have the same
parent data; the conversion below changes no vertex or quantity. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

def travelTree:Rounding.Tree (Fintype.card (Vertex A L)) where
  parent:=(tree A L).parent
  root:=(tree A L).root
  lower:=(tree A L).lower

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

def Q (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):ℝ:=
  HierarchicalQuota.quota hw H hr maps q hk (numbering A L v).1 (numbering A L v).2 t ω

def region (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):Finset Y:=
  univ.filter (HierarchyCounts.hit (maps t ω) (numbering A L v).2)

omit [Fintype Y] in
lemma Q_root (t:ℕ) (ω:Ω):Q A L hw H hr maps q hk t ω 0=k:=by
  exact congrArg (fun u:Vertex A L=>HierarchicalQuota.quota hw H hr maps q hk u.1.val u.2 t ω)
    (numbering_zero A L)

omit [Fintype Y] in
lemma Q_nonneg (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    0≤Q A L hw H hr maps q hk t ω v:=
  HierarchicalQuota.quota_nonneg hw H hr maps q hk hwpos _ t ω

omit [Fintype Y] in
lemma Q_children (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    (∑ u:(tree A L).Child v,Q A L hw H hr maps q hk t ω u.val)≤Q A L hw H hr maps q hk t ω v:=by
  by_cases hv:(numbering A L v).1.val<L
  · unfold Q
    rw [children_sum A L v (fun u:Vertex A L=>HierarchicalQuota.quota hw H hr maps q hk u.1.val u.2 t ω) hv]
    exact HierarchicalQuota.children_budget hw H hr maps q hk hwpos (numbering A L v).2 t ω
  · have he:(numbering A L v).1.val=L:=by have :=(numbering A L v).1.isLt; omega
    unfold Q
    rw [children_sum_leaf A L v (fun u:Vertex A L=>HierarchicalQuota.quota hw H hr maps q hk u.1.val u.2 t ω) he]
    exact Q_nonneg A L hw H hr maps q hk hwpos t ω v

omit [Fintype Y] in
lemma Q_adapted (t:ℕ) (v:Fin (Fintype.card (Vertex A L))):
    RankTracking.Adapted (H t) (fun ω=>Q A L hw H hr maps q hk t ω v):=by
  intro ω ρ he
  exact HierarchicalQuota.quota_adapted hw H hr maps q hk _ _ t ω ρ he

lemma Q_mass (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω) (v:Fin (Fintype.card (Vertex A L))):
    Q A L hw H hr maps q hk t ω v≤
      72*∑ y∈region A L maps t ω v,PosteriorCounting.measure (w:=w) (H t) (q t) ω y:=by
  exact (HierarchicalQuota.quota_bounds hw H hr maps q hk hwpos _ _ t ω).2.trans
    (mul_le_mul_of_nonneg_left (PosteriorCounting.size_prefix_bound hw H hr maps q _ t ω (hwpos ω) hm)
      (by norm_num))

lemma Q_witness (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω) (v:Fin (Fintype.card (Vertex A L)))
    (hq:0<Q A L hw H hr maps q hk t ω v):∃ y,y∈region A L maps t ω v:=by
  have hh:=Q_mass A L hw H hr maps q hk hwpos t ω hm v
  by_contra hn
  have he:region A L maps t ω v=∅:=by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hn ⟨y,hy⟩
  rw [he,sum_empty,mul_zero] at hh
  linarith

omit [Fintype Y] in
lemma park_nonneg (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    0≤(travelTree A L).park (Q A L hw H hr maps q hk t ω) v:=by
  apply sub_nonneg.mpr
  exact Q_children A L hw H hr maps q hk hwpos t ω v

omit [Fintype Y] in
lemma park_le_Q (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    (travelTree A L).park (Q A L hw H hr maps q hk t ω) v≤Q A L hw H hr maps q hk t ω v:=by
  apply sub_le_self
  exact sum_nonneg fun u _=>Q_nonneg A L hw H hr maps q hk hwpos t ω u.val

end KServer.PrefixTree

namespace KServer.Rounding
variable {n:ℕ} [NeZero n]
lemma Tree.under_root (T:Tree n) (v:Fin n):T.under 0 v=true:=by
  by_cases hv:v=0
  · subst v; exact T.under_self 0
  · rw [Tree.under,ite_eq_right hv,dite_eq_right hv]
    exact T.under_root (T.parent v)
termination_by v.val
decreasing_by exact T.lower v hv

lemma Tree.park_total (T:Tree n) (q:Fin n→ℝ):(∑ v,T.park q v)=q 0:=by
  have h:=T.park_subtree_total q 0
  simpa only [Tree.indicator,T.under_root,↓reduceIte,one_mul] using h
end KServer.Rounding

end


/-! Actual truncation ancestors of complete-prefix words, with the retained
numbering used by the finite rounding tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

def take (v:Vertex A L) (d:ℕ) (hd:d≤v.1.val):Vertex A L:=
  ⟨⟨d,lt_of_le_of_lt hd v.1.isLt⟩,fun i=>v.2 ⟨i.val,lt_of_lt_of_le i.isLt hd⟩⟩

omit [Fintype A] in
lemma take_self (v:Vertex A L):take A L v v.1.val le_rfl=v:=by
  rcases v with ⟨j,f⟩
  rfl

omit [Fintype A] in
lemma parent_depth (v:Vertex A L) (hv:0<v.1.val):
    (parent A L v).1.val=v.1.val-1:=by
  simp only [parent,dite_eq_right (by omega:v.1.val≠0)]

omit [Fintype A] in
lemma take_parent (v:Vertex A L) {d:ℕ} (hd:d<v.1.val):
    take A L (parent A L v) d (by rw [parent_depth A L v (by omega)]; omega)=
      take A L v d hd.le:=by
  rcases v with ⟨⟨e,he⟩,f⟩
  cases e with
  | zero=>exact False.elim (Nat.not_lt_zero _ hd)
  | succ e=>rfl

omit [Fintype A] in
lemma hit_take {Y:Type} (maps:ℕ→Y→A) (v:Vertex A L) (d:ℕ) (hd:d≤v.1.val)
    (y:Y) (hy:HierarchyCounts.hit maps v.2 y):
    HierarchyCounts.hit maps (take A L v d hd).2 y:=by
  intro i
  exact hy ⟨i.val,lt_of_lt_of_le i.isLt hd⟩

lemma numbering_parent (v:Fin (Fintype.card (Vertex A L))):
    numbering A L ((travelTree A L).parent v)=parent A L (numbering A L v):=by
  exact (numbering A L).apply_symm_apply _

lemma numbering_eq_root (v:Fin (Fintype.card (Vertex A L))):
    numbering A L v=root A L ↔ v=0:=by
  rw [←numbering_zero A L]
  exact (numbering A L).injective.eq_iff

lemma take_under (v:Fin (Fintype.card (Vertex A L))) (d:ℕ) (hd:d≤(numbering A L v).1.val):
    (travelTree A L).under ((numbering A L).symm (take A L (numbering A L v) d hd)) v=true:=by
  by_cases he:d=(numbering A L v).1.val
  · subst d
    rw [take_self,OrderIso.symm_apply_apply]
    exact (travelTree A L).under_self v
  · have hlt:d<(numbering A L v).1.val:=by omega
    have hv:v≠0:=by
      intro he
      subst v
      rw [numbering_zero] at hlt
      exact Nat.not_lt_zero _ hlt
    have hne:v≠(numbering A L).symm (take A L (numbering A L v) d hd):=by
      intro hh
      have hhh:=congrArg (fun u=>(numbering A L u).1.val) hh
      rw [OrderIso.apply_symm_apply] at hhh
      exact he hhh.symm
    rw [Rounding.Tree.under,ite_eq_right hne,dite_eq_right hv]
    have hp:d≤(numbering A L ((travelTree A L).parent v)).1.val:=by
      rw [numbering_parent,parent_depth A L _ (by omega)]
      omega
    have ht:take A L (numbering A L ((travelTree A L).parent v)) d hp=
        take A L (numbering A L v) d hd:=by
      simpa only [numbering_parent] using take_parent A L (numbering A L v) hlt
    rw [←ht]
    exact take_under ((travelTree A L).parent v) d hp
termination_by v.val
decreasing_by exact (travelTree A L).lower v hv

end KServer.PrefixTree

end


/-! Cumulative parked mass in the actual prefix cut is bounded by posterior
mass of the 67-radius ball. Selection can depend on the completed state. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

omit [Fintype A] in
lemma eq_of_common_hit {Y:Type} (maps:ℕ→Y→A) (u v:Vertex A L)
    (hd:u.1.val=v.1.val) (y:Y) (hu:HierarchyCounts.hit maps u.2 y)
    (hv:HierarchyCounts.hit maps v.2 y):u=v:=by
  rcases u with ⟨j,f⟩
  rcases v with ⟨j',g⟩
  have hj:j=j':=Fin.ext hd
  subst j'
  congr
  funext i
  exact (hu i).symm.trans (hv i)

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

theorem park_ball_capacity (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω)
    (S:Finset (Fin (Fintype.card (Vertex A L)))) (d:ℕ) (y:Y) (r:ℝ)
    (hd:∀ u∈S,d≤(numbering A L u).1.val)
    (hwit:∀ u∈S,∃ z∈region A L maps t ω u,dist y z≤27*r)
    (hdiam:∀ v:Fin (Fintype.card (Vertex A L)),(numbering A L v).1.val=d→
      ∀ a∈region A L maps t ω v,∀ b∈region A L maps t ω v,dist a b≤40*r):
    (∑ u∈S,(travelTree A L).park (Q A L hw H hr maps q hk t ω) u)≤
      72*Rounding.countingMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω)
        (univ.filter (fun z=>dist y z≤67*r)):=by
  let anc:S→Fin (Fintype.card (Vertex A L)):=fun u=>
    (numbering A L).symm (take A L (numbering A L u.val) d (hd u.val u.property))
  let F:Finset (Fin (Fintype.card (Vertex A L))):=univ.image anc
  have hdepth:∀ v∈F,(numbering A L v).1.val=d:=by
    intro v hv
    obtain ⟨u,_,rfl⟩:=mem_image.mp hv
    simp only [anc,OrderIso.apply_symm_apply,take]
  have hcover:∀ u∈S,∃ v∈F,(travelTree A L).under v u=true:=by
    intro u hu
    refine ⟨anc ⟨u,hu⟩,mem_image.mpr ⟨⟨u,hu⟩,mem_univ _,rfl⟩,?_⟩
    exact take_under A L u d (hd u hu)
  have hdisj:Set.PairwiseDisjoint (↑F) (region A L maps t ω):=by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    apply hne
    apply (numbering A L).injective
    exact eq_of_common_hit A L (maps t ω) _ _ ((hdepth u hu).trans (hdepth v hv).symm) z
      (mem_filter.mp hz).2 (mem_filter.mp hz').2
  have hwitness:∀ v∈F,∃ z∈region A L maps t ω v,dist y z≤27*r:=by
    intro v hv
    obtain ⟨u,_,rfl⟩:=mem_image.mp hv
    obtain ⟨z,hz,hclose⟩:=hwit u.val u.property
    refine ⟨z,?_,hclose⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [show numbering A L (anc u)=take A L (numbering A L u.val) d (hd u.val u.property) from
      OrderIso.apply_symm_apply _ _]
    exact hit_take A L (maps t ω) _ d _ z (mem_filter.mp hz).2
  exact (travelTree A L).geometric_park_capacity _
    (park_nonneg A L hw H hr maps q hk hwpos t ω) S F hcover (region A L maps t ω)
    _ (PosteriorCounting.measure_nonneg hw (H t) (q t) ω) (by norm_num) y
    (fun v _=>Q_mass A L hw H hr maps q hk hwpos t ω hm v) hdisj hwitness
    (fun v hv=>hdiam v (hdepth v hv))

end KServer.PrefixTree

end


/-! Literal variation of all parks, including the root park, with the exact
parent-edge factor. No metric or rounding movement estimate is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n:ℕ} [NeZero n]

lemma Tree.park_difference (T:Tree n) (q q':Fin n→ℝ) (v:Fin n):
    |T.park q' v-T.park q v|≤|q' v-q v|+∑ u:T.Child v,|q' u.val-q u.val|:=by
  have hh: T.park q' v-T.park q v=(q' v-q v)-∑ u:T.Child v,(q' u.val-q u.val):=by
    rw [sum_sub_distrib]
    unfold Tree.park
    ring
  rw [hh]
  exact (abs_sub _ _).trans (add_le_add (le_refl _) (abs_sum_le_sum_abs _ _))

lemma Tree.weighted_park_variation (T:Tree n) (q q' R:Fin n→ℝ)
    (hR:∀ v,0≤R v) (hroot:q' 0=q 0) {τ:ℝ} (hτ:0<τ)
    (hgeom:∀ v,v≠0→R (T.parent v)=τ*R v):
    (∑ v,R v*|T.park q' v-T.park q v|)≤
      (1+1/τ)*(∑ v,R (T.parent v)*|q' v-q v|):=by
  let f:=fun v=>|q' v-q v|
  have hf:f 0=0:=by simp [f,hroot]
  have he:(∑ v,R v*f v)=(1/τ)*(∑ v,R (T.parent v)*f v):=by
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    by_cases hv:v=0
    · simp [hv,hf]
    · rw [hgeom v hv]
      field_simp
  have hb:=sum_le_sum (s:=univ) (fun v (_:v∈univ)=>
    mul_le_mul_of_nonneg_left (T.park_difference q q' v) (hR v))
  simp only [mul_add,sum_add_distrib] at hb
  change _≤(∑ v,R v*f v)+(∑ v,R v*∑ u:T.Child v,f u.val) at hb
  rw [T.weighted_children R f hf,he] at hb
  convert hb using 1
  ring
end KServer.Rounding

namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

lemma sum_vertices (f:(d:ℕ)→(Fin d→A)→ℝ):
    (∑ v:Fin (Fintype.card (Vertex A L)),f (numbering A L v).1.val (numbering A L v).2)=
      ∑ d∈range (L+1),∑ word:Fin d→A,f d word:=by
  calc _ = ∑ u:Vertex A L,f u.1.val u.2:=
          Fintype.sum_equiv (numbering A L).toEquiv _ _ (fun _=>rfl)
       _ = (∑ d:Fin (L+1),∑ word:Fin d.val→A,f d.val word):=by rw [Fintype.sum_sigma]
       _ = _:=Fin.sum_univ_eq_sum_range (fun d=>∑ word:Fin d→A,f d word) (L+1)

end KServer.PrefixTree

end


/-! Fixed last-key bands in the complete prefix tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

abbrev Node:=Fin (Fintype.card (Vertex A L))
def depth (v:Node A L):ℕ:=(numbering A L v).1.val
def lastKey (v:Node A L):Option A:=
  if h:0<depth A L v then some ((numbering A L v).2 ⟨depth A L v-1,by change depth A L v-1<depth A L v; omega⟩) else none

def band (d:ℕ) (a:A):Finset (Node A L):=
  univ.filter (fun v=>depth A L v=d+1 ∧ lastKey A L v=some a)

def bandMass (p:Node A L→ℝ) (d:ℕ) (a:A):ℝ:=∑ v∈band A L d a,p v

lemma band_nonneg {p:Node A L→ℝ} (hp:∀ v,0≤p v) (d:ℕ) (a:A):
    0≤bandMass A L p d a:=sum_nonneg (fun v _=>hp v)

lemma band_key {Y:Type} (maps:ℕ→Y→A) (d:ℕ) (a:A) {v:Node A L}
    (hv:v∈band A L d a) (y:Y) (hy:HierarchyCounts.hit maps (numbering A L v).2 y):
    maps d y=a:=by
  obtain ⟨hd,ha⟩:=(mem_filter.mp hv).2
  have hp:0<depth A L v:=by omega
  simp only [lastKey,dite_eq_left hp,Option.some.injEq] at ha
  have hi:=hy ⟨depth A L v-1,by change depth A L v-1<depth A L v; omega⟩
  dsimp only at hi
  have he:depth A L v-1=d:=by omega
  rw [←ha,←hi,he]

lemma band_depth (d:ℕ) (a:A) {v:Node A L} (hv:v∈band A L d a):
    (numbering A L v).1.val=d+1:=(mem_filter.mp hv).2.1

lemma band_disjoint {Y:Type} [Fintype Y] (maps:ℕ→Y→A) (d:ℕ) (a:A):
    Set.PairwiseDisjoint (↑(band A L d a))
      (fun v=>univ.filter (HierarchyCounts.hit maps (numbering A L v).2)):=by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  apply hne
  apply (numbering A L).injective
  exact eq_of_common_hit A L maps _ _ ((band_depth A L d a hu).trans (band_depth A L d a hv).symm) z
    (mem_filter.mp hz).2 (mem_filter.mp hz').2

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

omit [MetricSpace Y] in
lemma band_capacity (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω) (d:ℕ) (a:A):
    bandMass A L ((travelTree A L).park (Q A L hw H hr maps q hk t ω)) d a≤
      72*Rounding.countingMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω)
        (univ.filter (fun y=>maps t ω d y=a)):=by
  have h:=sum_le_sum (s:=band A L d a) (fun v (_:v∈band A L d a)=>
    (park_le_Q A L hw H hr maps q hk hwpos t ω v).trans
      (Q_mass A L hw H hr maps q hk hwpos t ω hm v))
  change bandMass A L _ d a≤∑ v∈band A L d a,72*Rounding.countingMass
    (PosteriorCounting.measure (w:=w) (H t) (q t) ω) (region A L maps t ω v) at h
  rw [←mul_sum] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Rounding.disjoint_counting_mass (PosteriorCounting.measure_nonneg hw (H t) (q t) ω)
    (band_disjoint A L (maps t ω) d a)
  intro v hv y hy
  exact mem_filter.mpr ⟨mem_univ _,band_key A L (maps t ω) d a hv y (mem_filter.mp hy).2⟩

end KServer.PrefixTree

end


/-! Literal all-key persistent size references on the adapted complete map. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeyReferences
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (H:ℕ→Ω→ℕ) (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def count (d:ℕ) (a:A) (t:ℕ) (ω:Ω):ℝ:=∑ i:Fin k,if maps t ω d (q t ω i)=a then 1 else 0

omit [Fintype Ω] [Fintype A] [Fintype Y] in
lemma count_range (d:ℕ) (a:A) (t:ℕ) (ω:Ω):count maps q d a t ω∈Set.Icc 0 (k:ℝ):=by
  constructor
  · exact sum_nonneg fun i _=>by split_ifs <;> norm_num
  · have hh:=sum_le_sum (s:=(univ:Finset (Fin k))) (f:=fun i=>if maps t ω d (q t ω i)=a then (1:ℝ) else 0)
      (g:=fun _=>(1:ℝ)) (fun i _=>by split_ifs <;> norm_num)
    simpa [count] using hh

def size (d:ℕ) (a:A) (t:ℕ) (ω:Ω):ℝ:=1+posterior w (H t) (count maps q d a t) ω

def reference (d:ℕ) (a:A):ℕ→Ω→ℝ:=KeySizeTracking.held (size (w:=w) H maps q d a)

omit [Fintype A] in
lemma mass_eq (d:ℕ) (a:A) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω):
    (∑ y∈univ.filter (fun y=>maps t ω d y=a),PosteriorCounting.measure (w:=w) (H t) (q t) ω y)=
      posterior w (H t) (count maps q d a t) ω:=by
  have he:=PosteriorCounting.conditional_integral (w:=w) (H t) (q t) ω
    (fun ρ y=>if maps t ρ d y=a then (1:ℝ) else 0) (fun ρ h=>by funext y; rw [hm ρ h])
  unfold KeyReferences.count
  simpa only [sum_filter,mul_ite,mul_one,mul_zero] using he

variable (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)

def process (d:ℕ) (a:A):KeySizeTracking.FilteredSizes w ((k:ℝ)+1):=
  PosteriorSizes.process hw hwpos H hr (count maps q d a) (count_range maps q d a)

include hw hwpos hr
omit [Fintype A] [Fintype Y] in
lemma size_range (d:ℕ) (a:A) (t:ℕ) (ω:Ω):size (w:=w) H maps q d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  (process H maps q hw hwpos hr d a).range t ω

omit [Fintype A] [Fintype Y] in
lemma reference_range (d:ℕ) (a:A) (t:ℕ) (ω:Ω):
    reference (w:=w) H maps q d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  KeySizeTracking.held_range (size_range H maps q hw hwpos hr d a) t ω

omit [Fintype A] [Fintype Y] in
lemma reference_pos (d:ℕ) (a:A) (t:ℕ) (ω:Ω):0<reference (w:=w) H maps q d a t ω:=
  lt_of_lt_of_le (by norm_num) (reference_range H maps q hw hwpos hr d a t ω).1

omit [Fintype A] [Fintype Y] in
lemma reference_comparison (d:ℕ) (a:A) (t:ℕ) (ω:Ω):
    (5/6:ℝ)*reference (w:=w) H maps q d a t ω≤ size (w:=w) H maps q d a t ω ∧
      size (w:=w) H maps q d a t ω≤ (6/5:ℝ)*reference (w:=w) H maps q d a t ω:=
  KeySizeTracking.held_accurate (fun t ω=>(by linarith [(size_range H maps q hw hwpos hr d a t ω).1])) t ω

omit [Fintype A] [Fintype Y] in
lemma reference_adapted (d:ℕ) (a:A) (t:ℕ):Adapted (H t) (reference (w:=w) H maps q d a t):=
  KeySizeTracking.held_adapted (process H maps q hw hwpos hr d a) t

omit [Fintype A] [Fintype Y] in
lemma refresh_budget (hw1:∑ ω,w ω=1) (d:ℕ) (a:A) (T:ℕ):
    (∑ t∈range T,avg w (KeySizeTracking.refreshCost (size (w:=w) H maps q d a) t))≤
      144*(1+Real.log ((k:ℝ)+1))*(∑ t∈range T,avg w (fun ω=>|count maps q d a (t+1) ω-count maps q d a t ω|))+
        288*((k:ℝ)+1)*(1+(1+Real.log ((k:ℝ)+1))):=
  PosteriorSizes.refresh_budget hw hwpos hw1 (Nat.cast_nonneg k) H hr
    (count maps q d a) (count_range maps q d a) T

end KServer.KeyReferences

end


/- Height-independent scale-capacity estimates use summation by parts rather than dyadic grouping. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ParkedCoefficients

def tail (b : ℕ → ℝ) (n i : ℕ) : ℝ := ∑ j ∈ Ico i n, b j

lemma tail_zero (b : ℕ → ℝ) (n : ℕ) : tail b n n=0 := by simp [tail]
lemma tail_step (b : ℕ → ℝ) {n i : ℕ} (hi : i < n) :
    tail b n i=b i+tail b n (i+1) := by
  unfold tail
  exact Finset.sum_eq_sum_Ico_succ_bot hi b

lemma logarithmic_increment {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)/b ≤ Real.log b-Real.log a := by
  have hb := ha.trans_le hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  convert h using 1
  field_simp

lemma summation_by_parts (b A : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, b i/A i) = tail b n 0/A 0 +
      ∑ i ∈ range n, tail b n (i+1)*(1/A (i+1)-1/A i) := by
  have hstep : ∀ i ∈ range n, b i/A i =
      tail b n i/A i-tail b n (i+1)/A (i+1)+
      tail b n (i+1)*(1/A (i+1)-1/A i) := by
    intro i hi
    rw [tail_step b (mem_range.mp hi)]
    ring
  simp_rw [Finset.sum_congr rfl hstep, sum_add_distrib,
    Finset.sum_range_sub',tail_zero,zero_div,sub_zero]

/-- Positive tail capacities control reciprocal-weighted mass logarithmically.
The extra endpoint A n may be chosen as A (n-1), or any smaller positive value. -/
theorem capacity_log_sum {b A : ℕ → ℝ} {n : ℕ} {C K : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i ≤ n, A i ∈ Set.Icc 1 K)
    (hdec : ∀ i < n, A (i+1) ≤ A i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*A i) :
    ∑ i ∈ range n, b i/A i ≤ C*(1+Real.log K) := by
  have hp i (hi : i ≤ n) : 0 < A i := by linarith [(hA i hi).1]
  have ht : ∀ i ∈ range n, tail b n (i+1)*(1/A (i+1)-1/A i) ≤
      C*(Real.log (A i)-Real.log (A (i+1))) := by
    intro i hi
    have hin := mem_range.mp hi
    have h1 : 0 ≤ 1/A (i+1)-1/A i := sub_nonneg.mpr
      (one_div_le_one_div_of_le (hp (i+1) (by omega)) (hdec i hin))
    calc _ ≤ C*A (i+1)*(1/A (i+1)-1/A i) :=
          mul_le_mul_of_nonneg_right (hcap (i+1) (by omega)) h1
         _ = C*((A i-A (i+1))/A i) := by
          field_simp [(hp i (by omega)).ne',(hp (i+1) (by omega)).ne']
         _ ≤ _ := mul_le_mul_of_nonneg_left
          (logarithmic_increment (hp (i+1) (by omega)) (hdec i hin)) hC
  have h0 : tail b n 0/A 0 ≤ C := (div_le_iff₀ (hp 0 (by omega))).mpr (hcap 0 (by omega))
  rw [summation_by_parts]
  have hs := sum_le_sum ht
  rw [←mul_sum,Finset.sum_range_sub'] at hs
  have hlog0 := Real.log_le_log (hp 0 (by omega)) (hA 0 (by omega)).2
  have hlogn := Real.log_nonneg (hA n le_rfl).1
  have hh := mul_le_mul_of_nonneg_left (show Real.log (A 0)-Real.log (A n) ≤ Real.log K by linarith) hC
  linarith

lemma tail_mono {b c : ℕ → ℝ} {n i : ℕ} (h : ∀ j < n, b j ≤ c j) :
    tail b n i ≤ tail c n i := by
  apply sum_le_sum
  intro j hj
  exact h j (mem_Ico.mp hj).2

/-- Exact abstract form of §08's geometric estimate. b is selected parked mass,
d its held key size, B=1+mass(B(y,r)), A=1+mass(B(y,67r)). The assumptions here
are pointwise capacity data, not stochastic or policy-existence interfaces. -/
theorem park_coefficients {b d A B : ℕ → ℝ} {n : ℕ} {C K ρ R L : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, 0 < d i)
    (hA : ∀ i ≤ n, A i ∈ Set.Icc 1 K)
    (hB : ∀ i < n, B i ∈ Set.Icc 1 (A i))
    (hdec : ∀ i < n, A (i+1) ≤ A i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*A i)
    (hnorm : ∀ i < n, B i ≤ ρ*d i)
    (hbound : ∀ i < n, b i/d i ≤ R)
    (hlog : ∑ i ∈ range n, Real.log (A i/B i) ≤ L) :
    ∑ i ∈ range n, b i/d i ≤ R*L/Real.log 2+2*ρ*C*(1+Real.log K) := by
  let good : ℕ → ℝ := fun i => if A i ≤ 2*B i then b i else 0
  have hpA i (hi : i ≤ n) : 0 < A i := by linarith [(hA i hi).1]
  have hpB i (hi : i < n) : 0 < B i := by linarith [(hB i hi).1]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg : ∀ i < n, good i ≤ b i := by
    intro i hi; dsimp [good]; split_ifs <;> [rfl; exact hb i hi]
  have hgc := capacity_log_sum hC hA hdec (fun i hi =>
    (tail_mono hg).trans (hcap i hi))
  have hstep : ∀ i ∈ range n, b i/d i ≤
      R/Real.log 2*Real.log (A i/B i)+2*ρ*(good i/A i) := by
    intro i hi
    have hin := mem_range.mp hi
    have hln : 0 ≤ Real.log (A i/B i) := Real.log_nonneg
      ((one_le_div (hpB i hin)).mpr (hB i hin).2)
    by_cases hh : A i ≤ 2*B i
    · have hrad : A i ≤ 2*ρ*d i := hh.trans (by nlinarith [hnorm i hin])
      have hw : b i/d i ≤ 2*ρ*(b i/A i) := by
        apply (div_le_iff₀ (hd i hin)).mpr
        have hm := mul_le_mul_of_nonneg_left hrad (hb i hin)
        have he : 2*ρ*(b i/A i)*d i = (b i*(2*ρ*d i))/A i := by ring
        rw [he]
        apply (le_div_iff₀ (hpA i (by omega))).mpr
        simpa [mul_assoc] using hm
      dsimp only [good]
      rw [ite_eq_left hh]
      exact hw.trans (le_add_of_nonneg_left (mul_nonneg (div_nonneg hR h2.le) hln))
    · have hratio : 2 ≤ A i/B i := (le_div_iff₀ (hpB i hin)).mpr (le_of_not_ge hh)
      have hln2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hratio
      have ht : R ≤ R/Real.log 2*Real.log (A i/B i) := by
        have h := mul_le_mul_of_nonneg_left hln2 (div_nonneg hR h2.le)
        simpa [div_mul_cancel₀ R h2.ne'] using h
      dsimp only [good]
      rw [ite_eq_right hh,zero_div,mul_zero,add_zero]
      exact (hbound i hin).trans ht
  have hs := sum_le_sum hstep
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hs
  have hlu := mul_le_mul_of_nonneg_left hlog (div_nonneg hR h2.le)
  have hgu := mul_le_mul_of_nonneg_left hgc (by positivity : 0 ≤ 2*ρ)
  calc _ ≤ R/Real.log 2*L+2*ρ*(C*(1+Real.log K)) := hs.trans (add_le_add hlu hgu)
       _ = _ := by ring

/-- The exact fixed-offset telescope; scales shorter than the offset are included. -/
lemma scale_log_telescope {A B : ℕ → ℝ} {n p : ℕ} {K : ℝ}
    (hK : 1 ≤ K) (hA : ∀ i < n, A i ∈ Set.Icc 1 K)
    (hB : ∀ i < n, B i ∈ Set.Icc 1 K)
    (hshift : ∀ i < n, p ≤ i → A i ≤ B (i-p)) :
    ∑ i ∈ range n, Real.log (A i/B i) ≤ (p:ℝ)*Real.log K := by
  have hlogK := Real.log_nonneg hK
  have hlogB : ∀ i < n, 0 ≤ Real.log (B i) := fun i hi => Real.log_nonneg (hB i hi).1
  have hrewrite : (∑ i ∈ range n, Real.log (A i/B i)) =
      (∑ i ∈ range n, Real.log (A i))-(∑ i ∈ range n, Real.log (B i)) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have ha : 0 < A i := by linarith [(hA i (mem_range.mp hi)).1]
    have hb : 0 < B i := by linarith [(hB i (mem_range.mp hi)).1]
    exact Real.log_div ha.ne' hb.ne'
  rw [hrewrite]
  by_cases hpn : p ≤ n
  · have hfirst : ∑ i ∈ range p, Real.log (A i) ≤ (p:ℝ)*Real.log K := by
      calc _ ≤ ∑ _i ∈ range p, Real.log K := by
            apply sum_le_sum
            intro i hi
            have hin : i < n := (mem_range.mp hi).trans_le hpn
            exact Real.log_le_log (by linarith [(hA i hin).1]) (hA i hin).2
           _ = _ := by simp
    have hlast : ∑ i ∈ range (n-p), Real.log (A (p+i)) ≤
        ∑ i ∈ range (n-p), Real.log (B i) := by
      apply sum_le_sum
      intro i hi
      have hin : p+i < n := by have := mem_range.mp hi; omega
      have hh := hshift (p+i) hin (by omega)
      simp only [Nat.add_sub_cancel_left] at hh
      exact Real.log_le_log (by linarith [(hA (p+i) hin).1]) hh
    have htail : ∑ i ∈ range (n-p), Real.log (B i) ≤ ∑ i ∈ range n, Real.log (B i) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro i hi _
      exact hlogB i (mem_range.mp hi)
    have he := Finset.sum_range_add (fun i => Real.log (A i)) p (n-p)
    rw [Nat.add_sub_of_le hpn] at he
    linarith
  · have hupper : ∑ i ∈ range n, Real.log (A i) ≤ (n:ℝ)*Real.log K := by
      calc _ ≤ ∑ _i ∈ range n, Real.log K := by
            apply sum_le_sum
            intro i hi
            exact Real.log_le_log (by linarith [(hA i (mem_range.mp hi)).1]) (hA i (mem_range.mp hi)).2
           _ = _ := by simp
    have hnon := sum_nonneg (fun i hi => hlogB i (mem_range.mp hi))
    have hnp : (n:ℝ) ≤ p := by exact_mod_cast (le_of_not_ge hpn)
    nlinarith

/-- Source offset p=7 gives an absolute height-independent bound. The capacity
estimate is slightly relaxed from C*(A-1) to C*A, but the conclusion is the exact
O(1+log K) needed and the stronger source capacity implies this premise. -/
theorem seven_scale_park_coefficients {b d A B : ℕ → ℝ} {n : ℕ} {C K ρ R : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 ≤ R) (hK : 1 ≤ K)
    (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, 0 < d i)
    (hA : ∀ i ≤ n, A i ∈ Set.Icc 1 K)
    (hB : ∀ i < n, B i ∈ Set.Icc 1 (A i))
    (hdec : ∀ i < n, A (i+1) ≤ A i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*(A i-1))
    (hnorm : ∀ i < n, B i ≤ ρ*d i)
    (hbound : ∀ i < n, b i/d i ≤ R)
    (hshift : ∀ i < n, 7 ≤ i → A i ≤ B (i-7)) :
    ∑ i ∈ range n, b i/d i ≤ (7*R/Real.log 2+2*ρ*C)*(1+Real.log K) := by
  have hlog := scale_log_telescope hK (fun i hi => hA i hi.le)
    (fun i hi => ⟨(hB i hi).1,(hB i hi).2.trans (hA i hi.le).2⟩) hshift
  have h := park_coefficients hC hρ hR hb hd hA hB hdec
    (fun i hi => (hcap i hi).trans (by nlinarith)) hnorm hbound hlog
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := div_nonneg hR h2.le
  have hdiff : R*((7:ℕ):ℝ)*Real.log K/Real.log 2 + 2*ρ*C*(1+Real.log K) ≤
      (7*R/Real.log 2+2*ρ*C)*(1+Real.log K) := by
    calc _ = (7*R/Real.log 2+2*ρ*C)*(1+Real.log K)-7*(R/Real.log 2) := by norm_num; ring
         _ ≤ _ := sub_le_self _ (by positivity)
  calc _ ≤ R*((7:ℕ)*Real.log K)/Real.log 2+2*ρ*C*(1+Real.log K) := h
       _ = R*((7:ℕ):ℝ)*Real.log K/Real.log 2+2*ρ*C*(1+Real.log K) := by ring
       _ ≤ _ := hdiff

end KServer.ParkedCoefficients

namespace KServer.ParkedCoefficients
section MetricScales
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

/-- The manuscript's posterior measure of a closed metric ball, as a finite
counting sum. We do not restrict to distinct hidden locations. -/
def ballMass (μ : Y → ℝ) (y : Y) (r : ℝ) : ℝ :=
  ∑ z, if dist y z ≤ r then μ z else 0

lemma ballMass_nonneg {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : Y) (r : ℝ) :
    0 ≤ ballMass μ y r := by
  apply sum_nonneg
  intro z _
  split_ifs <;> [exact hμ z; rfl]

lemma ballMass_total {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : Y) (r : ℝ) :
    ballMass μ y r ≤ ∑ z, μ z := by
  apply sum_le_sum
  intro z _
  split_ifs <;> [rfl; exact hμ z]

lemma ballMass_mono {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : Y)
    {r s : ℝ} (hrs : r ≤ s) : ballMass μ y r ≤ ballMass μ y s := by
  apply sum_le_sum
  intro z _
  split_ifs with h h' h' <;> first | rfl | exact hμ z | (exfalso; exact h' (h.trans hrs))

def radius (r₀ τ : ℝ) (i : ℕ) := r₀/τ^i

lemma radius_pos {r₀ τ : ℝ} (hr : 0 < r₀) (hτ : 0 < τ) (i : ℕ) :
    0 < radius r₀ τ i := div_pos hr (pow_pos hτ i)

lemma radius_antitone {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 1 ≤ τ) :
    Antitone (radius r₀ τ) := by
  intro i j hij
  have hp : 0 < τ := by linarith
  exact div_le_div_of_nonneg_left hr (pow_pos hp i) (pow_le_pow_right₀ hτ hij)

lemma radius_seven {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 2 ≤ τ) {i : ℕ} (hi : 7 ≤ i) :
    67*radius r₀ τ i ≤ radius r₀ τ (i-7) := by
  have hp : 0 < τ := by linarith
  have hpow : (67:ℝ) ≤ τ^7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hτ 7
    norm_num at hh
    linarith
  unfold radius
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hp i) (pow_pos hp (i-7))).mpr
  have he : τ^i=τ^(i-7)*τ^7 := by rw [←pow_add,Nat.sub_add_cancel hi]
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hpow (mul_nonneg hr (pow_nonneg hp.le (i-7)))
  nlinarith

/-- The pointwise coefficient bound now for the actual metric ball masses and
geometric scales of §07-08, not an assumed logarithmic telescope. b is zero on
unselected levels. Cumulative subcapacity is supplied by Tree.geometric_park_capacity;
held normalization and individual domination are the exact local invariants. -/
theorem metric_park_coefficients {μ : Y → ℝ} (hμ : ∀ z, 0 ≤ μ z)
    (y : Y) {k C ρ R r₀ τ : ℝ} {n : ℕ} {b d : ℕ → ℝ}
    (hmass : ∑ z, μ z=k) (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hr : 0 ≤ r₀) (hτ : 2 ≤ τ)
    (hb : ∀ i < n, 0 ≤ b i) (hd : ∀ i < n, 0 < d i)
    (hcap : ∀ i ≤ n, tail b n i ≤ C*ballMass μ y (67*radius r₀ τ i))
    (hnorm : ∀ i < n, 1+ballMass μ y (radius r₀ τ i) ≤ ρ*d i)
    (hbound : ∀ i < n, b i/d i ≤ R) :
    ∑ i ∈ range n, b i/d i ≤ (7*R/Real.log 2+2*ρ*C)*(1+Real.log (k+1)) := by
  let A := fun i => 1+ballMass μ y (67*radius r₀ τ i)
  let B := fun i => 1+ballMass μ y (radius r₀ τ i)
  have hk : 0 ≤ k := by rw [←hmass]; exact sum_nonneg (fun z _ => hμ z)
  have hrad : ∀ i, 0 ≤ radius r₀ τ i := fun i => div_nonneg hr (pow_nonneg (by linarith) i)
  have hAB : ∀ i, B i ≤ A i := by
    intro i
    dsimp [A,B]
    have h := ballMass_mono hμ y (show radius r₀ τ i ≤ 67*radius r₀ τ i by nlinarith [hrad i])
    linarith
  have hA : ∀ i ≤ n, A i ∈ Set.Icc 1 (k+1) := by
    intro i _
    have hn := ballMass_nonneg hμ y (67*radius r₀ τ i)
    have ht := ballMass_total hμ y (67*radius r₀ τ i)
    rw [hmass] at ht
    dsimp [A]
    constructor <;> linarith
  have hB : ∀ i < n, B i ∈ Set.Icc 1 (A i) := by
    intro i _
    exact ⟨by dsimp [B]; linarith [ballMass_nonneg hμ y (radius r₀ τ i)],hAB i⟩
  have hdec : ∀ i < n, A (i+1) ≤ A i := by
    intro i _
    have hh := radius_antitone hr (show 1 ≤ τ by linarith) (show i ≤ i+1 by omega)
    have hm := ballMass_mono hμ y (show 67*radius r₀ τ (i+1) ≤ 67*radius r₀ τ i by linarith)
    dsimp [A]; linarith
  have hshift : ∀ i < n, 7 ≤ i → A i ≤ B (i-7) := by
    intro i _ hi
    have hm := ballMass_mono hμ y (radius_seven hr hτ hi)
    dsimp [A,B]; linarith
  apply seven_scale_park_coefficients hC hρ hR (by linarith) hb hd hA hB hdec _ hnorm hbound hshift
  intro i hi
  simpa [A] using hcap i hi

end MetricScales
end KServer.ParkedCoefficients

end


/-! All finer selected last-key bands form a literal prefix cut. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

def selectedBand (sel:ℕ→Option A) (d:ℕ):Finset (Node A L):=
  match sel d with | none =>∅ | some a =>band A L d a

def selectedMass (p:Node A L→ℝ) (sel:ℕ→Option A) (d:ℕ):ℝ:=
  ∑ v∈selectedBand A L sel d,p v

lemma selected_depth (sel:ℕ→Option A) {d:ℕ} {v:Node A L}
    (hv:v∈selectedBand A L sel d):depth A L v=d+1:=by
  unfold selectedBand at hv
  cases he:sel d with
  | none=>rw [he] at hv; exact (notMem_empty _ hv).elim
  | some a=>rw [he] at hv; exact band_depth A L d a hv

lemma selected_disjoint (sel:ℕ→Option A) (F:Finset ℕ):
    Set.PairwiseDisjoint (↑F) (selectedBand A L sel):=by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hd:=selected_depth A L sel hi
  have hd':=selected_depth A L sel hj
  omega

lemma selected_tail (p:Node A L→ℝ) (sel:ℕ→Option A) (j:ℕ):
    ParkedCoefficients.tail (selectedMass A L p sel) L j=
      ∑ v∈(Ico j L).biUnion (selectedBand A L sel),p v:=by
  rw [sum_biUnion (selected_disjoint A L sel (Ico j L))]
  rfl

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

theorem selected_capacity (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω)
    (sel:ℕ→Option A) (y:Y) {R τ:ℝ} (hR:0≤R) (hτ:2≤τ)
    (hclose:∀ i a,sel i=some a→∀ z,maps t ω i z=a→
      dist y z≤27*ParkedCoefficients.radius R τ i)
    (hcells:∀ i a b,maps t ω i a=maps t ω i b→
      dist a b≤40*ParkedCoefficients.radius R τ i) (j:ℕ):
    ParkedCoefficients.tail
      (selectedMass A L ((travelTree A L).park (Q A L hw H hr maps q hk t ω)) sel) L j≤
      72*ParkedCoefficients.ballMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω) y
        (67*ParkedCoefficients.radius R τ j):=by
  let p:Node A L→ℝ:=(travelTree A L).park (Q A L hw H hr maps q hk t ω)
  let F:Finset (Node A L):=(Ico j L).biUnion (selectedBand A L sel)
  let S:=F.filter (fun v=>0<p v)
  have hn:∀ v,0≤p v:=park_nonneg A L hw H hr maps q hk hwpos t ω
  have he:(∑ v∈F,p v)=(∑ v∈S,p v):=by
    symm
    apply sum_subset (filter_subset _ _)
    intro v hv hvs
    have hh:¬0<p v:=by simpa only [S,mem_filter,hv,true_and] using hvs
    exact le_antisymm (le_of_not_gt hh) (hn v)
  rw [selected_tail]
  change (∑ v∈F,p v)≤_
  rw [he]
  have hd:∀ v∈S,j+1≤(numbering A L v).1.val:=by
    intro v hv
    obtain ⟨i,hi,hvi⟩:=mem_biUnion.mp (mem_filter.mp hv).1
    have hvd:=selected_depth A L sel hvi
    have hij:=(mem_Ico.mp hi).1
    change j+1≤depth A L v
    omega
  have hwi:∀ v∈S,∃ z∈region A L maps t ω v,
      dist y z≤27*ParkedCoefficients.radius R τ j:=by
    intro v hv
    obtain ⟨i,hi,hvi⟩:=mem_biUnion.mp (mem_filter.mp hv).1
    have hp:0<Q A L hw H hr maps q hk t ω v:=
      lt_of_lt_of_le (mem_filter.mp hv).2 (park_le_Q A L hw H hr maps q hk hwpos t ω v)
    obtain ⟨z,hz⟩:=Q_witness A L hw H hr maps q hk hwpos t ω hm v hp
    refine ⟨z,hz,?_⟩
    unfold selectedBand at hvi
    cases hs:sel i with
    | none=>rw [hs] at hvi; exact (notMem_empty _ hvi).elim
    | some a=>
      rw [hs] at hvi
      exact (hclose i a hs z (band_key A L (maps t ω) i a hvi z (mem_filter.mp hz).2)).trans
        (mul_le_mul_of_nonneg_left (ParkedCoefficients.radius_antitone hR (by linarith)
          (mem_Ico.mp hi).1) (by norm_num))
  have hdia:∀ v:Node A L,(numbering A L v).1.val=j+1→
      ∀ a∈region A L maps t ω v,∀ b∈region A L maps t ω v,
        dist a b≤40*ParkedCoefficients.radius R τ j:=by
    intro v hv a ha b hb
    have hj:j<(numbering A L v).1.val:=by omega
    apply hcells
    exact ((mem_filter.mp ha).2 ⟨j,hj⟩).trans ((mem_filter.mp hb).2 ⟨j,hj⟩).symm
  have hh:=park_ball_capacity A L hw H hr maps q hk hwpos t ω hm S (j+1) y
    (ParkedCoefficients.radius R τ j) hd hwi hdia
  simpa only [Rounding.countingMass,ParkedCoefficients.ballMass,sum_filter] using hh

end KServer.PrefixTree

end


/-! The actual prefix parks satisfy the logarithmic coefficient estimate.
The denominator is the held persistent slot size; empty selected levels vanish. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

lemma selected_mass_nonneg {p:Node A L→ℝ} (hp:∀ v,0≤p v) (sel:ℕ→Option A) (j:ℕ):
    0 ≤ selectedMass A L p sel j:=sum_nonneg (fun v _=>hp v)

lemma ballMass_eq (μ:Y→ℝ) (y:Y) (r:ℝ):
    ParkedCoefficients.ballMass μ y r=Rounding.countingMass μ (univ.filter (fun z=>dist y z≤r)):=by
  simp only [ParkedCoefficients.ballMass,Rounding.countingMass,sum_filter]

def selectedDenominator (μ:Y→ℝ) (y:Y) (r:ℕ→ℝ) (sel:ℕ→Option A) (u:ℕ→A→ℝ) (i:ℕ):ℝ:=
  match sel i with | none =>1+ParkedCoefficients.ballMass μ y (r i) | some a =>u i a

theorem selected_coefficients (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω)
    (hm:∀ ρ,H t ρ=H t ω→maps t ρ=maps t ω)
    (sel:ℕ→Option A) (y:Y) (u:ℕ→A→ℝ) {R τ:ℝ} (hR:0≤R) (hτ:2≤τ)
    (hu:∀ i a,0<u i a)
    (hnorm:∀ i a,1+Rounding.countingMass (PosteriorCounting.measure (w:=w) (H t) (q t) ω)
      (univ.filter (fun z=>maps t ω i z=a))≤(6/5:ℝ)*u i a)
    (hclose:∀ i a,sel i=some a→∀ z,maps t ω i z=a→
      dist y z≤27*ParkedCoefficients.radius R τ i)
    (hcontains:∀ i a,sel i=some a→∀ z,dist y z≤ParkedCoefficients.radius R τ i→maps t ω i z=a)
    (hcells:∀ i a b,maps t ω i a=maps t ω i b→
      dist a b≤40*ParkedCoefficients.radius R τ i):
    let p:Node A L→ℝ:=(travelTree A L).park (Q A L hw H hr maps q hk t ω)
    let μ:=PosteriorCounting.measure (w:=w) (H t) (q t) ω
    ∑ i∈range L,selectedMass A L p sel i/
      selectedDenominator A μ y (ParkedCoefficients.radius R τ) sel u i≤
        (7*((6/5:ℝ)*72)/Real.log 2+2*(6/5:ℝ)*72)*(1+Real.log ((k:ℝ)+1)):=by
  dsimp only
  let μ:=PosteriorCounting.measure (w:=w) (H t) (q t) ω
  let p:Node A L→ℝ:=(travelTree A L).park (Q A L hw H hr maps q hk t ω)
  have hμ:∀ z,0≤μ z:=PosteriorCounting.measure_nonneg hw (H t) (q t) ω
  let den:=selectedDenominator A μ y (ParkedCoefficients.radius R τ) sel u
  have hd:∀ i,0<den i:=by
    intro i
    dsimp [den,selectedDenominator]
    cases hs:sel i with
    | none=>simp only; linarith [ParkedCoefficients.ballMass_nonneg hμ y (ParkedCoefficients.radius R τ i)]
    | some a=>exact hu i a
  have hn:∀ i,1+ParkedCoefficients.ballMass μ y (ParkedCoefficients.radius R τ i)≤(6/5:ℝ)*den i:=by
    intro i
    dsimp [den,selectedDenominator]
    cases hs:sel i with
    | none=>simp only; nlinarith [ParkedCoefficients.ballMass_nonneg hμ y (ParkedCoefficients.radius R τ i)]
    | some a=>
      have hb:ParkedCoefficients.ballMass μ y (ParkedCoefficients.radius R τ i)≤
          Rounding.countingMass μ (univ.filter (fun z=>maps t ω i z=a)):=by
        rw [ballMass_eq]
        apply sum_le_sum_of_subset_of_nonneg
        · intro z hz
          exact mem_filter.mpr ⟨mem_univ _,hcontains i a hs z (mem_filter.mp hz).2⟩
        · intro z _ _; exact hμ z
      exact (add_le_add_right hb 1).trans (hnorm i a)
  have hb:∀ i,selectedMass A L p sel i/den i≤(6/5:ℝ)*72:=by
    intro i
    dsimp [selectedMass,selectedBand,den,selectedDenominator]
    cases hs:sel i with
    | none=>simp only [sum_empty,zero_div]; norm_num
    | some a=>
      change bandMass A L p i a/u i a≤(6/5:ℝ)*72
      apply (div_le_iff₀ (hu i a)).mpr
      have hh:=band_capacity A L hw H hr maps q hk hwpos t ω hm i a
      have hn:=hnorm i a
      dsimp only [p] at *
      nlinarith
  exact ParkedCoefficients.metric_park_coefficients hμ y
    (PosteriorCounting.measure_total hw (H t) (q t) ω (hwpos ω))
    (by norm_num : (0:ℝ)≤72) (by norm_num : (0:ℝ)<6/5) (by norm_num : (0:ℝ)≤(6/5:ℝ)*72)
    hR hτ (fun i _=>selected_mass_nonneg A L (park_nonneg A L hw H hr maps q hk hwpos t ω) sel i)
    (fun i _=>hd i) (fun i _=>selected_capacity A L hw H hr maps q hk hwpos t ω hm sel y hR hτ hclose hcells i)
    (fun i _=>hn i) (fun i _=>hb i)
end KServer.PrefixTree

end


/-! Literal allocation and persistent bands on the single positive experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointAllocation
open JointExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

abbrev Ω:=JointExperiment.Atom (k:=k) law hr
abbrev A:=LevelKeys.Key Y k
local instance keyDecEq : DecidableEq (A (Y:=Y) (k:=k)) := Classical.decEq _

def quota (t:ℕ) (ω:Ω (k:=k) law hr):PrefixTree.Node (A (Y:=Y) (k:=k)) L→ℝ:=
  PrefixTree.Q _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk t ω

def park (t:ℕ) (ω:Ω (k:=k) law hr):PrefixTree.Node (A (Y:=Y) (k:=k)) L→ℝ:=
  (PrefixTree.travelTree _ L).park (quota s law hr hk t ω)

def band (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):ℝ:=
  PrefixTree.bandMass _ L (park s law hr hk t ω) d a

def size (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):ℝ:=
  KeyReferences.size (w:=weight law hr) (history law hr) (maps law hr s) (hidden law hr s) d a t ω

def reference (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):ℝ:=
  KeySizeTracking.held (size s law hr d a) t ω

lemma quota_nonneg (t:ℕ) (ω:Ω (k:=k) law hr) (v:PrefixTree.Node (A (Y:=Y) (k:=k)) L):
    0≤quota s law hr hk t ω v:=
  PrefixTree.Q_nonneg _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω v

lemma park_nonneg (t:ℕ) (ω:Ω (k:=k) law hr) (v:PrefixTree.Node (A (Y:=Y) (k:=k)) L):
    0≤park s law hr hk t ω v:=
  PrefixTree.park_nonneg _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω v

lemma band_nonneg (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):
    0≤band s law hr hk t ω d a:=PrefixTree.band_nonneg _ L (park_nonneg s law hr hk t ω) d a

lemma band_capacity (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):
    band s law hr hk t ω d a≤72*(size s law hr d a t ω-1):=by
  have hm:∀ ρ,history law hr t ρ=history law hr t ω→maps law hr s t ρ=maps law hr s t ω:=
    fun ρ h=>maps_adapted law hr s t ρ ω h
  have hh:=PrefixTree.band_capacity _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω hm d a
  unfold Rounding.countingMass at hh
  rw [KeyReferences.mass_eq] at hh
  · simpa only [band,park,quota,size,KeyReferences.size,add_sub_cancel_left] using hh
  · exact hm

lemma size_range (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    size s law hr d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  KeyReferences.size_range (history law hr) (maps law hr s) (hidden law hr s)
    (weight_nonneg law hr) (weight_pos law hr) (history_refines law hr) d a t ω

lemma reference_range (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    reference s law hr d a t ω∈Set.Icc 1 ((k:ℝ)+1):=
  KeySizeTracking.held_range (size_range s law hr d a) t ω

lemma reference_pos (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    0<reference s law hr d a t ω:=by linarith [(reference_range s law hr d a t ω).1]

lemma reference_comparison (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    (5/6:ℝ)*reference s law hr d a t ω≤ size s law hr d a t ω ∧
      size s law hr d a t ω≤ (6/5:ℝ)*reference s law hr d a t ω:=
  KeyReferences.reference_comparison (history law hr) (maps law hr s) (hidden law hr s)
    (weight_nonneg law hr) (weight_pos law hr) (history_refines law hr) d a t ω

lemma coefficient_bounds (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):
    band s law hr hk t ω d a/reference s law hr d a t ω∈Set.Icc 0 ((6/5:ℝ)*72):=by
  constructor
  · exact div_nonneg (band_nonneg s law hr hk t ω d a) (reference_pos s law hr d a t ω).le
  · apply (div_le_iff₀ (reference_pos s law hr d a t ω)).mpr
    have hh:=band_capacity s law hr hk t ω d a
    have hn:=(reference_comparison s law hr d a t ω).2
    nlinarith

lemma quota_adapted (t:ℕ) (ω ρ:Ω (k:=k) law hr) (h:history law hr t ω=history law hr t ρ):
    quota s law hr hk t ω=quota s law hr hk t ρ:=by
  funext v
  exact PrefixTree.Q_adapted _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk t v ω ρ h

lemma band_adapted (t:ℕ) (ω ρ:Ω (k:=k) law hr) (h:history law hr t ω=history law hr t ρ):
    band s law hr hk t ω=band s law hr hk t ρ:=by
  unfold band park
  rw [quota_adapted s law hr hk t ω ρ h]

lemma reference_adapted (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ):
    Adapted (history law hr t) (reference s law hr d a t):=
  KeyReferences.reference_adapted (history law hr) (maps law hr s) (hidden law hr s)
    (weight_nonneg law hr) (weight_pos law hr) (history_refines law hr) d a t

lemma size_mass_joint (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    size s law hr d a t ω=1+∑ y∈univ.filter (fun y=>maps law hr s t ω d y=a),
      PosteriorCounting.measure (w:=weight law hr) (history law hr t) (hidden law hr s t) ω y:=by
  change 1+_=1+_
  exact congrArg (fun z:ℝ=>1+z) (KeyReferences.mass_eq (w:=weight law hr) (history law hr) (maps law hr s)
    (hidden law hr s) d a t ω (fun ρ h=>maps_adapted law hr s t ρ ω h)).symm

lemma size_mass (d:Fin L) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):
    size s law hr d.val a t ω=1+∑ y∈univ.filter (fun y=>LevelKeys.map s law (hr d).le
      ω.val.1 (ω.val.2 d) t y=a),FiniteExperiment.mu s law t ω.val.1 y:=by
  rw [size_mass_joint]
  have hm:maps law hr s t ω d.val=LevelKeys.map s law (hr d).le ω.val.1 (ω.val.2 d) t:=by
    funext y
    simp only [JointExperiment.maps,dite_eq_left d.isLt]
  rw [hm]
  apply congrArg (fun z:ℝ=>1+z)
  apply sum_congr rfl
  intro y _
  exact JointExperiment.measure_eq law hr s t ω y

end KServer.JointAllocation

end


/-! From the exact conditional allocation construction to levelwise hidden-key
changes. This counts both true hidden movement and changing online maps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open ActualCharges
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def keyCross (d t:ℕ) (ω:Ω):ℝ:=∑ l:Fin k,
  if maps (t+1) ω d (q (t+1) ω l)=maps t ω d (q t ω l) then 0 else 1

def keyTransport (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*total w N (keyCross maps q d)

def prefixTransport (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*total w N (prefixCross maps q (d+1))

omit [Fintype Ω] [Fintype A] in
lemma prefixCross_zero (t:ℕ) (ω:Ω):prefixCross maps q 0 t ω=0:=by
  have he:∀ l:Fin k,address maps q 0 (t+1) ω l=address maps q 0 t ω l:=by
    intro l
    funext i
    exact i.elim0
  simp [prefixCross,he]

omit [Fintype Ω] [Fintype A] in
lemma prefixCross_step (d t:ℕ) (ω:Ω):prefixCross maps q (d+1) t ω ≤
    prefixCross maps q d t ω+keyCross maps q d t ω:=by
  unfold prefixCross keyCross
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro l _
  by_cases ha:address maps q d (t+1) ω l=address maps q d t ω l
  · by_cases hb:maps (t+1) ω d (q (t+1) ω l)=maps t ω d (q t ω l)
    · have he:address maps q (d+1) (t+1) ω l=address maps q (d+1) t ω l:=by
        funext i
        exact Fin.lastCases (motive:=fun i:Fin (d+1)=>
          address maps q (d+1) (t+1) ω l i=address maps q (d+1) t ω l i)
          hb (fun j=>congrFun ha j) i
      simp [he,ha,hb]
    · simp only [ite_eq_left ha,ite_eq_right hb,zero_add]
      split_ifs <;> norm_num
  · simp only [ite_eq_right ha]
    split_ifs <;> norm_num

omit [Fintype A] in
include hw in
lemma prefix_transport_bound (r:ℕ→ℝ) (hrad:∀ d,0 ≤ r d)
    (hhalf:∀ d,r (d+1) ≤ r d/2) (L N:ℕ):
    prefixTransport (w:=w) maps q r L N ≤ 2*keyTransport (w:=w) maps q r L N:=by
  have hs:=sum_le_sum (s:=range L) (fun d _=>mul_le_mul_of_nonneg_left
    (total_mono hw (N:=N) (fun t ω=>prefixCross_step maps q d t ω)) (hrad d))
  simp only [total_add,mul_add,sum_add_distrib] at hs
  have hp:=weighted_shift r (fun d=>total w N (prefixCross maps q d)) hrad
    (fun d=>total_nonneg hw (fun t ω=>prefixCross_nonneg maps q d t ω))
    (by simp [total,prefixCross_zero,RankTracking.avg]) hhalf L
  change _ ≤ (1/2:ℝ)*prefixTransport maps q r L N at hp
  change prefixTransport maps q r L N ≤ _+keyTransport maps q r L N at hs
  linarith

include hw in
lemma tree_drift_bound (r:ℕ→ℝ) (hrad:∀ d,0 ≤ r d)
    (hhalf:∀ d,r (d+1) ≤ r d/2) (L N:ℕ):
    treeDrift hw H hr maps q r L N ≤ 6*keyTransport (w:=w) maps q r L N:=by
  have hc d:= (level_drift_count hw H hr maps q d N).trans (level_count_cross hw maps q d N)
  have hs:=sum_le_sum (s:=range L) (fun d _=>mul_le_mul_of_nonneg_left (hc (d+1)) (hrad d))
  have hp:=weighted_shift r (fun d=>levelDrift hw H hr maps q d N) hrad
    (fun d=>levelDrift_nonneg hw H hr maps q d N) (levelDrift_zero hw H hr maps q N) hhalf L
  have hx:=prefix_transport_bound hw maps q r hrad hhalf L N
  have hs':(∑ d∈range L,r d*levelDrift hw H hr maps q (d+1) N) ≤
      2*prefixTransport (w:=w) maps q r L N:=by
    simpa only [prefixTransport,mul_sum,mul_assoc,mul_comm,mul_left_comm] using hs
  unfold treeDrift
  simp only [mul_add,sum_add_distrib]
  -- The precise coefficient is six with these per-level estimates.
  linarith
end KServer.HierarchicalQuota

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
open RankTracking
variable {Ω I:Type} [Fintype Ω] [Fintype I] {w:Ω→ℝ}
lemma total_sum (N:ℕ) (f:I→ℕ→Ω→ℝ):
    total w N (fun t ω=>∑ i,f i t ω)=∑ i,total w N (f i):=by
  simp only [total,avg_sum]
  exact sum_comm
lemma avg_const_one (hw:∑ ω,w ω=1) (c:ℝ):avg w (fun _=>c)=c:=by
  unfold avg
  rw [←sum_mul,hw,one_mul]
end KServer.ActualCharges

end

end OAI
