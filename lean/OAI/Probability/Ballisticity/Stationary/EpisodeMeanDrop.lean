import Mathlib
import OAI.Probability.Ballisticity.Stationary.LocalEpisodeLog
import OAI.Probability.Ballisticity.Stationary.EpisodeDropLedger

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

theorem mean_episode_drops (hr : Monotone r) (hf : 0 ≤ fexp) (hb : 0 < b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u)
    (β : ℝ) (hbad : ∀ᵐ ω ∂Q, β*Real.log (N:ℝ) ≤ -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal)
    (hstages : 2*b*(∫ ω, (J ω N:ℝ) ∂Q) ≤ β/4*Real.log (N:ℝ))
    (L : ℕ) (hL : 0<L)
    (hcharge : ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) ≤ 2*b*L) :
    (3*β/4*Real.log (N:ℝ) ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(∫ ω, (M ω N:ℝ) ∂Q)) ∧
    ((∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1) ∧
    (β/2*Real.log (N:ℝ) ≤ ∫ ω, ∑ i ∈ Finset.range N, if j ω i ≤ L then c ω i else 0 ∂Q) := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  let S : Environment d → ℝ := fun ω => ∑ i ∈ Finset.range N, if j ω i≤L then c ω i else 0
  let B : Environment d → ℝ := fun ω => ∑ i ∈ Finset.range N, if L<j ω i then c ω i else 0
  let D : Environment d → ℝ := fun ω => -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal
  have hc (i : ℕ) := dropMark_integrable (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ Q hκ i
  have hsum : Integrable D Q := by
    have hh := integrable_finsetSum (s:=Finset.range N) (fun i _ => hc i)
    simpa only [dropMark_total] using hh
  have hS : Integrable S Q := by
    apply integrable_finsetSum
    intro i _
    convert (hc i).indicator (s:={ω | j ω i≤L}) (measurableSet_le (stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i) measurable_const) using 1
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  have hB : Integrable B Q := by
    apply integrable_finsetSum
    intro i _
    convert (hc i).indicator (s:={ω | L<j ω i}) (measurableSet_lt measurable_const (stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i)) using 1
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  have hJ := (counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N).1
  have hM := number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N
  have hdrop : β*Real.log (N:ℝ) ≤ ∫ ω, D ω ∂Q := by
    have := integral_mono_ae (integrable_const (β*Real.log (N:ℝ))) hsum hbad
    simpa only [integral_const,probReal_univ,one_smul] using this
  have htotal : (∫ ω, D ω ∂Q) ≤ A*(∫ ω, (M ω N:ℝ) ∂Q)+2*b*(∫ ω, (J ω N:ℝ) ∂Q) := by
    have hh := integral_mono_ae hsum ((hM.const_mul A).add (hJ.const_mul (2*b)))
      (hκ.mono (fun ω hω => total_drop_bound (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ ω hω))
    change (∫ ω, D ω ∂Q) ≤ (∫ ω, A*(M ω N:ℝ)+2*b*(J ω N:ℝ) ∂Q) at hh
    rw [integral_add (f:=fun ω => A*(M ω N:ℝ)) (g:=fun ω => 2*b*(J ω N:ℝ)) (hM.const_mul _) (hJ.const_mul _),
      integral_const_mul,integral_const_mul] at hh
    exact hh
  have hlower : 3*β/4*Real.log (N:ℝ) ≤ A*(∫ ω, (M ω N:ℝ) ∂Q) := by linarith
  have hupper : (∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1 := by
    have hcount := integral_mono hM (hJ.add (integrable_const 1)) (fun ω => by
      change (M ω N:ℝ) ≤ (J ω N:ℝ)+1
      exact_mod_cast (number_stage_bound (k:=k) e f hef r fexp g χ b sfloor hR N ω N).1)
    change (∫ ω, (M ω N:ℝ) ∂Q) ≤ (∫ ω, (J ω N:ℝ)+1 ∂Q) at hcount
    rw [integral_add (f:=fun ω => (J ω N:ℝ)) (g:=fun _ => (1:ℝ)) hJ (integrable_const _)] at hcount
    simp only [integral_const,probReal_univ,one_smul] at hcount
    have hjle : (∫ ω, (J ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b) := by
      apply (le_div_iff₀ (show 0<8*b by positivity)).mpr
      nlinarith only [hstages]
    linarith
  have hlong : (∫ ω, B ω ∂Q) ≤ β/2*Real.log (N:ℝ) := by
    have hl : (∫ ω, B ω ∂Q) ≤ (A/(L:ℝ)+2*b)*(∫ ω, (J ω N:ℝ) ∂Q) := by
      have hh := integral_mono_ae hB (hJ.const_mul (A/(L:ℝ)+2*b))
        (hκ.mono (fun ω hω => long_drop_bound (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ ω hω L hL))
      rw [integral_const_mul] at hh
      exact hh
    have hcoeff : A/(L:ℝ) ≤ 2*b := (div_le_iff₀ (Nat.cast_pos.mpr hL)).mpr hcharge
    have hnon : 0 ≤ ∫ ω, (J ω N:ℝ) ∂Q := integral_nonneg (fun _ => Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hcoeff hnon
    nlinarith only [hl,hm,hstages]
  have hsplit : (∫ ω, S ω ∂Q)+(∫ ω, B ω ∂Q)=(∫ ω, D ω ∂Q) := by
    rw [←integral_add hS hB]
    apply integral_congr_ae
    filter_upwards [] with ω
    change S ω+B ω=D ω
    dsimp only [S,B,D]
    rw [←Finset.sum_add_distrib,←dropMark_total (k:=k) e f hef r fexp g χ b sfloor hR N ω]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hh : j ω i≤L
    · simp only [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · simp only [ite_eq_right hh,ite_eq_left (Nat.lt_of_not_ge hh),zero_add]
  exact ⟨hlower,hupper,by change β/2*Real.log (N:ℝ) ≤ ∫ ω, S ω ∂Q; linarith⟩

end DirectionalTransience.EpisodeChainLedger

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience
namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma dropMark_bounds_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) (i : ℕ) :
    0 ≤ c ω i ∧ c ω i ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*
        (if T ω i<N then 1 else 0)+2*b*(j ω i) := by
  by_cases ha : T ω i<N
  · have hh := episode_log_bound_local e f hef r fexp g χ b sfloor hr hR N (T ω i)
      hf hb hs ω hH κ hκ0 hκ1 hκ hk hbκ
    simpa only [dropMark,stepMark,episodeBoundary,ite_eq_left ha,mul_one,episodeStageCount] using hh
  · simp only [dropMark,stepMark,episodeBoundary,ite_eq_right ha,sub_self,mul_zero,Nat.cast_zero,add_zero,le_refl,and_self]

lemma total_drop_bound_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(M ω N)+2*b*(J ω N) := by
  rw [←dropMark_total]
  have hh := Finset.sum_le_sum (s:=Finset.range N) (fun i _ =>
    (dropMark_bounds_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hκ i).2)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hh
  have hm : (∑ i ∈ Finset.range N, if T ω i<N then (1:ℝ) else 0)=(M ω N:ℝ) := by
    exact_mod_cast (number_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N).symm
  have hj : (∑ i ∈ Finset.range N, (j ω i:ℝ))=(J ω N:ℝ) := by
    exact_mod_cast stepMark_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  rw [hm,hj] at hh
  exact hh

lemma long_drop_bound_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
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
      have hc := (dropMark_bounds_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hκ i).2
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

lemma dropMark_integrable_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) (i : ℕ) : Integrable (fun ω => c ω i) Q := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  apply Integrable.of_bound (dropMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i).aestronglyMeasurable (A+2*b*N)
  filter_upwards [hκ] with ω hω
  have hc := dropMark_bounds_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hω i
  rw [Real.norm_eq_abs,abs_of_nonneg hc.1]
  have hA : 0 ≤ A := injection_cost_nonneg (k:=k) r sfloor κ hκ0 hκ1
  have hj : (j ω i:ℝ) ≤ N := by exact_mod_cast stepMark_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
  have hai : A*(if T ω i<N then (1:ℝ) else 0) ≤ A := by split <;> simp_all only [mul_one,mul_zero,le_refl]
  have hc' : c ω i ≤ A*(if T ω i<N then 1 else 0)+2*b*(j ω i) := hc.2
  have := mul_le_mul_of_nonneg_left hj (show 0≤2*b by positivity)
  linarith

theorem mean_episode_drops_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 < b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u)
    (β : ℝ) (hbad : ∀ᵐ ω ∂Q, β*Real.log (N:ℝ) ≤ -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal)
    (hstages : 2*b*(∫ ω, (J ω N:ℝ) ∂Q) ≤ β/4*Real.log (N:ℝ))
    (L : ℕ) (hL : 0<L)
    (hcharge : ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) ≤ 2*b*L) :
    (3*β/4*Real.log (N:ℝ) ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(∫ ω, (M ω N:ℝ) ∂Q)) ∧
    ((∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1) ∧
    (β/2*Real.log (N:ℝ) ≤ ∫ ω, ∑ i ∈ Finset.range N, if j ω i ≤ L then c ω i else 0 ∂Q) := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  let S : Environment d → ℝ := fun ω => ∑ i ∈ Finset.range N, if j ω i≤L then c ω i else 0
  let B : Environment d → ℝ := fun ω => ∑ i ∈ Finset.range N, if L<j ω i then c ω i else 0
  let D : Environment d → ℝ := fun ω => -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal
  have hc (i : ℕ) := dropMark_integrable_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ Q hκ i
  have hsum : Integrable D Q := by
    have hh := integrable_finsetSum (s:=Finset.range N) (fun i _ => hc i)
    simpa only [dropMark_total] using hh
  have hS : Integrable S Q := by
    apply integrable_finsetSum
    intro i _
    convert (hc i).indicator (s:={ω | j ω i≤L}) (measurableSet_le (stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i) measurable_const) using 1
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  have hB : Integrable B Q := by
    apply integrable_finsetSum
    intro i _
    convert (hc i).indicator (s:={ω | L<j ω i}) (measurableSet_lt measurable_const (stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i)) using 1
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  have hJ := (counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N).1
  have hM := number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N
  have hdrop : β*Real.log (N:ℝ) ≤ ∫ ω, D ω ∂Q := by
    have := integral_mono_ae (integrable_const (β*Real.log (N:ℝ))) hsum hbad
    simpa only [integral_const,probReal_univ,one_smul] using this
  have htotal : (∫ ω, D ω ∂Q) ≤ A*(∫ ω, (M ω N:ℝ) ∂Q)+2*b*(∫ ω, (J ω N:ℝ) ∂Q) := by
    have hh := integral_mono_ae hsum ((hM.const_mul A).add (hJ.const_mul (2*b)))
      (hκ.mono (fun ω hω => total_drop_bound_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ ω hω))
    change (∫ ω, D ω ∂Q) ≤ (∫ ω, A*(M ω N:ℝ)+2*b*(J ω N:ℝ) ∂Q) at hh
    rw [integral_add (f:=fun ω => A*(M ω N:ℝ)) (g:=fun ω => 2*b*(J ω N:ℝ)) (hM.const_mul _) (hJ.const_mul _),
      integral_const_mul,integral_const_mul] at hh
    exact hh
  have hlower : 3*β/4*Real.log (N:ℝ) ≤ A*(∫ ω, (M ω N:ℝ) ∂Q) := by linarith
  have hupper : (∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1 := by
    have hcount := integral_mono hM (hJ.add (integrable_const 1)) (fun ω => by
      change (M ω N:ℝ) ≤ (J ω N:ℝ)+1
      exact_mod_cast (number_stage_bound (k:=k) e f hef r fexp g χ b sfloor hR N ω N).1)
    change (∫ ω, (M ω N:ℝ) ∂Q) ≤ (∫ ω, (J ω N:ℝ)+1 ∂Q) at hcount
    rw [integral_add (f:=fun ω => (J ω N:ℝ)) (g:=fun _ => (1:ℝ)) hJ (integrable_const _)] at hcount
    simp only [integral_const,probReal_univ,one_smul] at hcount
    have hjle : (∫ ω, (J ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b) := by
      apply (le_div_iff₀ (show 0<8*b by positivity)).mpr
      nlinarith only [hstages]
    linarith
  have hlong : (∫ ω, B ω ∂Q) ≤ β/2*Real.log (N:ℝ) := by
    have hl : (∫ ω, B ω ∂Q) ≤ (A/(L:ℝ)+2*b)*(∫ ω, (J ω N:ℝ) ∂Q) := by
      have hh := integral_mono_ae hB (hJ.const_mul (A/(L:ℝ)+2*b))
        (hκ.mono (fun ω hω => long_drop_bound_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ ω hω L hL))
      rw [integral_const_mul] at hh
      exact hh
    have hcoeff : A/(L:ℝ) ≤ 2*b := (div_le_iff₀ (Nat.cast_pos.mpr hL)).mpr hcharge
    have hnon : 0 ≤ ∫ ω, (J ω N:ℝ) ∂Q := integral_nonneg (fun _ => Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hcoeff hnon
    nlinarith only [hl,hm,hstages]
  have hsplit : (∫ ω, S ω ∂Q)+(∫ ω, B ω ∂Q)=(∫ ω, D ω ∂Q) := by
    rw [←integral_add hS hB]
    apply integral_congr_ae
    filter_upwards [] with ω
    change S ω+B ω=D ω
    dsimp only [S,B,D]
    rw [←Finset.sum_add_distrib,←dropMark_total (k:=k) e f hef r fexp g χ b sfloor hR N ω]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hh : j ω i≤L
    · simp only [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · simp only [ite_eq_right hh,ite_eq_left (Nat.lt_of_not_ge hh),zero_add]
  exact ⟨hlower,hupper,by change β/2*Real.log (N:ℝ) ≤ ∫ ω, S ω ∂Q; linarith⟩

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
