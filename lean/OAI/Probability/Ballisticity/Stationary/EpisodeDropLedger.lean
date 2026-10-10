import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeGlobalRetention
import OAI.Probability.Ballisticity.Stationary.EpisodeCounterChain
import OAI.Probability.Ballisticity.Stationary.EpisodeNumber

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

noncomputable def stepMark (ω : Environment d) (i : ℕ) : ℕ :=
  if T ω i<N then episodeSteps e f hef r fexp g χ b sfloor N
    (episodeInitial (k:=k) e f hef r sfloor hR (T ω i) ω) ω N else 0

noncomputable def dropMark (ω : Environment d) (i : ℕ) : ℝ :=
  Real.log (crossingQuenched (realPosition (step e)) 0 (T ω i) ω).toReal-
    Real.log (crossingQuenched (realPosition (step e)) 0 (T ω (i+1)) ω).toReal
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_sub (ω : Environment d) (i : ℕ) : j ω i=J ω (i+1)-J ω i := by
  rw [steps,Nat.add_sub_cancel_left]
  rfl

lemma stepMark_measurable (i : ℕ) : Measurable (fun ω => j ω i) := by
  have hi := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i).fst
  have hj := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N (i+1)).fst
  have h : Measurable (fun ω => J ω (i+1)-J ω i) := hj.sub hi
  convert h using 1
  exact funext (fun ω => stepMark_sub (k:=k) e f hef r fexp g χ b sfloor hR N ω i)

lemma dropMark_measurable (i : ℕ) : Measurable (fun ω => c ω i) := by
  have hm : Measurable (fun p : Environment d×ℕ => crossingQuenched (realPosition (step e)) 0 p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro n
    simpa only [Prod.fst,Prod.snd] using (measurable_crossingQuenched (realPosition (step e)) 0 (n:ℝ))
  exact (((hm.comp (measurable_id.prodMk (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i))).ennreal_toReal.log).sub
    ((hm.comp (measurable_id.prodMk (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N (i+1)))).ennreal_toReal.log))

lemma stepMark_sum (ω : Environment d) (n : ℕ) : ∑ i ∈ Finset.range n, j ω i=J ω n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,steps]
  | succ n ih => rw [Finset.sum_range_succ,ih,steps]; rfl

lemma dropMark_sum (ω : Environment d) (n : ℕ) :
    ∑ i ∈ Finset.range n, c ω i = -Real.log (crossingQuenched (realPosition (step e)) 0 (T ω n) ω).toReal := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,episodeBoundary,Nat.cast_zero,
      crossingQuenched_zero,ENNReal.toReal_one,Real.log_one,neg_zero]
  | succ n ih => rw [Finset.sum_range_succ,ih,dropMark]; ring

lemma dropMark_total (ω : Environment d) :
    ∑ i ∈ Finset.range N, c ω i = -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal := by
  rw [dropMark_sum,episodeBoundary_complete]

lemma dropMark_bounds (hr : Monotone r) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) (i : ℕ) :
    0 ≤ c ω i ∧ c ω i ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*
        (if T ω i<N then 1 else 0)+2*b*(j ω i) := by
  by_cases ha : T ω i<N
  · have hh := episode_log_bound e f hef r hr fexp g χ b sfloor hR N (T ω i)
      hf hb hs ω hH κ hκ0 hκ1 hκ hk hbκ
    simpa only [dropMark,stepMark,episodeBoundary,ite_eq_left ha,mul_one,episodeStageCount] using hh
  · simp only [dropMark,stepMark,episodeBoundary,ite_eq_right ha,sub_self,mul_zero,Nat.cast_zero,add_zero,le_refl,and_self]

lemma total_drop_bound (hr : Monotone r) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(M ω N)+2*b*(J ω N) := by
  rw [←dropMark_total]
  have hh := Finset.sum_le_sum (s:=Finset.range N) (fun i _ =>
    (dropMark_bounds (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hκ i).2)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hh
  have hm : (∑ i ∈ Finset.range N, if T ω i<N then (1:ℝ) else 0)=(M ω N:ℝ) := by
    exact_mod_cast (number_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N).symm
  have hj : (∑ i ∈ Finset.range N, (j ω i:ℝ))=(J ω N:ℝ) := by
    exact_mod_cast stepMark_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  rw [hm,hj] at hh
  exact hh

end DirectionalTransience.EpisodeChainLedger

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_le (ω : Environment d) (i : ℕ) : j ω i ≤ N := by
  unfold stepMark
  split
  · exact (episode_counts_le_loops e f hef r fexp g χ b sfloor N _ ω
      (episodeStageFails e f r fexp g χ b N) N).1
  · exact Nat.zero_le _

lemma dropMark_inactive (ω : Environment d) (i : ℕ) (hi : M ω N ≤ i) : c ω i=0 := by
  have ha : ¬T ω i<N := by
    rw [active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω i]
    exact not_lt.mpr hi
  simp only [dropMark,episodeBoundary,ite_eq_right ha,sub_self]

lemma injection_cost_nonneg (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    0 ≤ ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) := by
  have hlog : Real.log (κ:ℝ) ≤ 0 := Real.log_nonpos hκ0.le hκ1
  exact mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.mpr hlog)

lemma long_drop_bound (hr : Monotone r) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) (L : ℕ) (hL : 0<L) :
    (∑ i ∈ Finset.range N, if L<j ω i then c ω i else 0) ≤
      (((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))/(L:ℝ)+2*b)*(J ω N) := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  have hA : 0 ≤ A := injection_cost_nonneg (k:=k) r sfloor κ hκ0 hκ1
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hp : 0 ≤ A/(L:ℝ)+2*b := by positivity
  have hpoint (i : ℕ) : (if L<j ω i then c ω i else 0) ≤ (A/(L:ℝ)+2*b)*(j ω i) := by
    split
    · rename_i hij
      have hjr : (L:ℝ) ≤ (j ω i:ℝ) := by exact_mod_cast hij.le
      have hratio : 1 ≤ (j ω i:ℝ)/(L:ℝ) := (one_le_div hLr).mpr hjr
      have hcharge : A ≤ A/(L:ℝ)*(j ω i:ℝ) := by
        have := mul_le_mul_of_nonneg_left hratio hA
        calc A = A*1 := (mul_one _).symm
             _ ≤ A*((j ω i:ℝ)/(L:ℝ)) := this
             _ = _ := by ring
      have hc := (dropMark_bounds (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hκ i).2
      have hai : A*(if T ω i<N then (1:ℝ) else 0) ≤ A := by split <;> simp_all only [mul_one,mul_zero,le_refl]
      change c ω i ≤ A*(if T ω i<N then 1 else 0)+2*b*(j ω i) at hc
      nlinarith only [hc,hai,hcharge]
    · exact mul_nonneg hp (Nat.cast_nonneg _)
  have h := Finset.sum_le_sum (s:=Finset.range N) (fun i _ => hpoint i)
  rw [←Finset.mul_sum] at h
  have hj : (∑ i ∈ Finset.range N, (j ω i:ℝ))=(J ω N:ℝ) := by
    exact_mod_cast stepMark_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  rw [hj] at h
  exact h

lemma dropMark_integrable (hr : Monotone r) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) (i : ℕ) : Integrable (fun ω => c ω i) Q := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  apply Integrable.of_bound (dropMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i).aestronglyMeasurable (A+2*b*N)
  filter_upwards [hκ] with ω hω
  have hc := dropMark_bounds (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hω i
  rw [Real.norm_eq_abs,abs_of_nonneg hc.1]
  have hA : 0 ≤ A := injection_cost_nonneg (k:=k) r sfloor κ hκ0 hκ1
  have hj : (j ω i:ℝ) ≤ N := by exact_mod_cast stepMark_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
  have hai : A*(if T ω i<N then (1:ℝ) else 0) ≤ A := by split <;> simp_all only [mul_one,mul_zero,le_refl]
  have hc' : c ω i ≤ A*(if T ω i<N then 1 else 0)+2*b*(j ω i) := hc.2
  have := mul_le_mul_of_nonneg_left hj (show 0≤2*b by positivity)
  linarith

end DirectionalTransience.EpisodeChainLedger

end

end OAI
