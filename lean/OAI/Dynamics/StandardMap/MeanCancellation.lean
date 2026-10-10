import OAI.Dynamics.StandardMap.MeanDeficit

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma cancellation_weight_sum (N : ℕ) :
    ∑ s∈Finset.range N, (2*(s:ℝ)+2)*(1/4:ℝ)^s ≤ 4 := by
  have hb (s : ℕ) : (s:ℝ)+1 ≤ (2:ℝ)^s := by
    induction s with
    | zero => norm_num
    | succ s ih => rw [pow_succ]; push_cast; nlinarith
  calc
    _ ≤ ∑ s∈Finset.range N, 2*(1/2:ℝ)^s := Finset.sum_le_sum fun s hs => by
      have hh := mul_le_mul_of_nonneg_right (hb s) (show 0 ≤ (1/4:ℝ)^s by positivity)
      rw [← mul_pow] at hh
      norm_num at hh
      nlinarith
    _ = 2*∑ s∈Finset.range N, (1/2:ℝ)^s := by rw [Finset.mul_sum]
    _ ≤ 4 := by
      have hh := sum_geometric_two_le N
      norm_num only [one_div] at *
      linarith
noncomputable def cancellationWeight (k : ℝ) (s : ℕ) (z : Torus) : ℝ :=
  if torusCancellation k s z then 2*(s:ℝ)+2 else 0
lemma cancellationWeight_eq_indicator (k : ℝ) (s : ℕ) :
    cancellationWeight k s={z | torusCancellation k s z}.indicator (fun _ => 2*(s:ℝ)+2) := by
  funext z
  simp only [cancellationWeight,Set.indicator_apply,Set.mem_ofPred_eq]
lemma integrable_cancellationWeight (k : ℝ) (s : ℕ) : Integrable (cancellationWeight k s) area := by
  rw [cancellationWeight_eq_indicator]
  exact (integrable_const _).indicator (isClosed_torusCancellation k s).measurableSet
lemma integral_cancellationWeight (k : ℝ) (s : ℕ) :
    (∫ z,cancellationWeight k s z ∂area)=(2*(s:ℝ)+2)*area.real {z | torusCancellation k s z} := by
  rw [cancellationWeight_eq_indicator,integral_indicator (isClosed_torusCancellation k s).measurableSet]
  simp [mul_comm]
lemma integral_cancellationWeight_le (k : ℝ) (C : ℝ) (hC : 0 ≤ C) (s : ℕ)
    (hc : area {z | torusCancellation k s z} ≤ ENNReal.ofReal (C*(1/4:ℝ)^s)) :
    (∫ z,cancellationWeight k s z ∂area) ≤ C*((2*(s:ℝ)+2)*(1/4:ℝ)^s) := by
  rw [integral_cancellationWeight]
  have hr : area.real {z | torusCancellation k s z} ≤ C*(1/4:ℝ)^s := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(s:ℝ)+2 by positivity)
  nlinarith
lemma integral_cancellationLoss_le (k : ℝ) (hk : 0 ≤ k) (n : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ s : ℕ, area {z | torusCancellation k s z} ≤ ENNReal.ofReal (C*(1/4:ℝ)^s)) :
    (∫ z,cancellationLoss k z n ∂area) ≤
      10000000000*(1+∫ z,wingDefect k z n ∂area)+4*C := by
  have hD : Integrable (fun z => wingDefect k z n) area :=
    (continuous_wingDefect k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun z => cancellationLoss k z n) area :=
    (continuous_cancellationLoss k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (fun z => ∑ s∈Finset.range (n+1), cancellationWeight k s z) area :=
    integrable_finsetSum _ (fun s hs => integrable_cancellationWeight k s)
  have ht : Integrable (fun z => 10000000000*(1+wingDefect k z n)) area :=
    ((integrable_const 1).add hD).const_mul _
  have hb (z : Torus) : cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)+∑ s∈Finset.range (n+1),cancellationWeight k s z :=
    cancellationLoss_pointwise_bound k hk z n
  have hh := integral_mono hl (ht.add hw) hb
  have hsum : (∫ z,10000000000*(1+wingDefect k z n)+∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area)=
      (∫ z,10000000000*(1+wingDefect k z n) ∂area)+(∫ z,∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area) := by
    convert! integral_add ht hw using 1
  have hDint : (∫ z,10000000000*(1+wingDefect k z n) ∂area)=10000000000*(1+∫ z,wingDefect k z n ∂area) := by
    rw [integral_const_mul]
    have he : (∫ z,1+wingDefect k z n ∂area)=1+∫ z,wingDefect k z n ∂area := by
      calc
        _ = (∫ _z : Torus,(1:ℝ) ∂area)+(∫ z,wingDefect k z n ∂area) := by
          convert! integral_add (integrable_const (1:ℝ)) hD using 1
        _ = _ := by simp
    rw [he]
  have hwint : (∫ z,∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area)=∑ s∈Finset.range (n+1),∫ z,cancellationWeight k s z ∂area := by
    convert! integral_finsetSum (Finset.range (n+1)) (fun s hs => integrable_cancellationWeight k s) using 1
  simp only [Pi.add_apply] at hh
  rw [hsum,hDint,hwint] at hh
  have hsumbd : (∑ s∈Finset.range (n+1),∫ z,cancellationWeight k s z ∂area) ≤ 4*C := by
    calc
      _ ≤ ∑ s∈Finset.range (n+1),C*((2*(s:ℝ)+2)*(1/4:ℝ)^s) :=
        Finset.sum_le_sum fun s hs => integral_cancellationWeight_le k C hC s (hc s)
      _ = C*∑ s∈Finset.range (n+1),(2*(s:ℝ)+2)*(1/4:ℝ)^s := by rw [Finset.mul_sum]
      _ ≤ 4*C := by nlinarith [mul_le_mul_of_nonneg_left (cancellation_weight_sum (n+1)) hC]
  linarith
noncomputable def doublingConstant : ℝ := 10000000001+4*cancellationConstant
lemma doublingConstant_pos : 0<doublingConstant := by
  unfold doublingConstant; nlinarith [cancellationConstant_pos]
lemma eventually_meanDeficit_doubling :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀ ≤ growthBase k → ∀ n : ℕ, 0<n →
      meanDeficit k n ≤ meanDeficit k (n+n) ∧
      meanDeficit k (n+n) ≤ doublingConstant*meanDeficit k n+doublingConstant/(n:ℝ) := by
  obtain ⟨M₀,hM⟩ := eventually_cancellation_area
  refine ⟨M₀,?_⟩
  intro k hk hMk n hn
  refine ⟨meanDeficit_doubling_mono k hk.le n hn,?_⟩
  have hb := integral_cancellationLoss_le k hk.le n cancellationConstant cancellationConstant_pos.le (hM k hk hMk)
  have hD := integral_wingDefect_le k hk.le n hn
  rw [integral_cancellationLoss k hk.le n hn] at hb
  have he := (meanDeficit_bounds k hk.le n hn).1
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc := cancellationConstant_pos
  unfold doublingConstant
  have hn0 : (0:ℝ)<n := by positivity
  apply (mul_le_mul_iff_right₀ hn0).mp
  rw [mul_add,mul_div_cancel₀ _ hn0.ne']
  have hx : 0 ≤ cancellationConstant*meanDeficit k n*(n:ℝ) := by positivity
  nlinarith
end StandardMapEntropy

end OAI
