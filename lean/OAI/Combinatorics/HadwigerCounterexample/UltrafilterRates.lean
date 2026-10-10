import OAI.Combinatorics.HadwigerCounterexample.ExponentialRates
import Mathlib.Order.Filter.Ultrafilter.Basic

namespace OAI

/-! # Ultrafilter Rates -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset
open scoped Topology

variable {A B : Type} {l : Filter A} {U : Ultrafilter A} {x y z v a : A → ℝ}

/-- Upper target thresholds, without claiming nonnegativity. -/
def slight (l : Filter A) (x : A→ℝ) := ∀ δ:ℝ,0<δ→∀ᶠ n in l,x n≤δ

theorem slight_gap :
    slight (U : Filter A) x ∨ ∃ δ:ℝ,0<δ∧∀ᶠ n in U, δ < x n := by
  by_cases h : slight (U : Filter A) x
  · exact Or.inl h
  right
  unfold slight at h

  push Not at h
  obtain ⟨δ,hd,h⟩:=h
  exact ⟨δ,hd,h⟩

/-- At least subexponential mass. -/
def warm (l : Filter A) (z x : A→ℝ) :=
  ∀ ε:ℝ,0<ε → ∀ᶠ i in l,bp (-ε * z i) ≤ x i

namespace warm

theorem const (hz : Tendsto z l atTop) {a : ℝ} (ha : 0<a) : warm l z (fun _=>a) := by
  intro ε he
  exact (((bp_tendsto_zero he).comp hz).eventually (gt_mem_nhds ha)).mono (fun _ h=> h.le)
theorem mono (h : warm l z x) (hg : ∀ᶠ i in l,x i≤ y i) : warm l z y := fun ε he=>
  (h ε he).mp (hg.mono fun _ hi h=>h.trans hi)
theorem positive (h : warm l z x) : ∀ᶠ i in l,0<x i :=
  (h 1 zero_lt_one).mono (fun _ hi => (bp_pos _).trans_le hi)

theorem mul (h : warm l z x) (hg : warm l z y) : warm l z (fun i=> x i*y i) := by
  intro ε he
  filter_upwards [h (ε/2) (half_pos he),hg (ε/2) (half_pos he)] with i hi hj
  rw [show -ε*z i= -(ε/2)*z i + -(ε/2)*z i from by ring,bp_add]
  exact mul_le_mul hi hj (bp_pos _).le ((bp_pos _).le.trans hi)
theorem inv_cap (h : warm l z x) : ExpO l z (fun i=> (x i)⁻¹) := by
  intro c hc
  filter_upwards [h c hc] with i hi
  rw [abs_of_nonneg (inv_nonneg.mpr ((bp_pos _).le.trans hi))]
  exact le_trans (inv_anti₀ (bp_pos _) hi) (le_of_eq (by rw [neg_mul,bp_neg,inv_inv]))

theorem survive (hz : Tendsto z l atTop) (h : warm l z x) (hg : ExpSmall l z y) :
    warm l z (fun i=> x i - y i) := by
  have he := (hg.mul h.inv_cap).lim hz
  refine ((const hz (by norm_num : 0<(1/2:ℝ))).mul h).mono ?_
  filter_upwards [h.positive,he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with i hi hg
  change y i*(x i)⁻¹<1/2 at hg
  rw [←div_eq_mul_inv] at hg
  linarith only [(div_lt_iff₀ hi).mp hg]
end warm

namespace ExpSmall
theorem bp_n {c : ℝ} (hc : 0<c) : ExpSmall l z (fun n=>bp (-c*z n)) :=
  ⟨_,hc,.of_forall (fun _ => (abs_of_pos (bp_pos _)).le)⟩

theorem poly (hz : Tendsto z l atTop) (hx : ExpSmall l z x) (k : ℕ) :
    ExpSmall l z (fun n=>x n*(z n)^k) := by
  refine hx.mul (fun ε he => ?_)
  have hp : ∀ᶠ n in l, 1*(z n)^(k:ℝ)< bp (ε*z n) :=
    hz.eventually (bp_poly_dom he _ _)
  filter_upwards [hp,hz.eventually (eventually_ge_atTop 0)] with n hn h
  rw [abs_of_nonneg (pow_nonneg h _),←Real.rpow_natCast]
  simpa only [one_mul] using hn.le

end ExpSmall

theorem taking {X : A→ Type*} [∀ n,Nonempty (X n)]
    {P : ∀ n,X n→Prop} (h : ∀ᶠ n in l,∃ w:X n,P n w) :
    ∃ w:∀ n,X n,∀ᶠ n in l,P n (w n) := by
  classical
  let f n:= if h:∃ w,P n w then h.choose else Classical.choice (inferInstance:Nonempty (X n))
  refine ⟨f,h.mono (fun n hn=>?_)⟩
  unfold f; rw [dite_eq_left hn]; exact hn.choose_spec

theorem diagonal_gains (l : Filter ℕ) (h : l ≤ atTop) (P : ℕ → ℕ→Prop)
    (hp : ∀ k,∀ᶠ n in l,P n k) :
    ∃ k:ℕ→ℕ,Tendsto k l atTop∧∀ᶠ n in l,P n (k n) := by
  classical
  let a (n : ℕ) : Finset ℕ := (Finset.range (n+1)).filter (P n)
  let k (n : ℕ) := if h:(a n).Nonempty then (a n).max' h else 0
  have he (n r : ℕ) (hr : r≤n) (hc : P n r) : P n (k n) ∧ r≤k n := by
    have hx : r∈a n := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    unfold k; rw [dite_eq_left ⟨r,hx⟩]
    exact ⟨(mem_filter.mp (Finset.max'_mem _ _)).2,Finset.le_max' _ _ hx⟩
  have heq r : ∀ᶠ n in l,P n (k n) ∧ r≤ k n :=
    (hp r).and ((eventually_ge_atTop r).filter_mono h) |>.mono (fun n ⟨hh,hx⟩=>he n r hx hh)
  exact ⟨k,tendsto_atTop.mpr (fun b=> (heq b).mono fun _=> And.right),(heq 0).mono fun _=> And.left⟩

theorem slight_inv_stage {f : ℕ→ℕ} {l : Filter ℕ} (hf : Tendsto f l atTop) :
    slight l (fun i=> ((f i:ℝ)+1)⁻¹) := by
  have h : Tendsto (fun i => (f i:ℝ)+1) l atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hf)
  intro ε he
  exact (h.inv_tendsto_atTop.eventually (gt_mem_nhds he)).mono fun n hn=>hn.le

theorem trend_sizes (l : Filter ℕ) (h : l ≤ atTop) {M : ℕ} (hM : 1≤ M) :
    Tendsto (fun n=> M*n) l atTop ∧ Tendsto (fun n=> ((M*n:ℕ):ℝ)) l atTop := by
  have hh : Tendsto (fun n : ℕ=> M*n) atTop atTop := tendsto_atTop.mpr (fun a =>
    (eventually_ge_atTop a).mono (fun k hk=> le_trans hk (by nlinarith)))
  exact ⟨hh.mono_left h, tendsto_natCast_atTop_atTop.comp (hh.mono_left h)⟩

end HadwigerCounterexample

end

end OAI
