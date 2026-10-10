import OAI.Probability.SLE.Multipoint.MultipointPhaseProcess

namespace OAI

/-! Only the integration intervals are capped at the localization horizon.
The phase continues to read the original switches, so an unreached switch
is not mistaken for completion at the horizon. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def horizonStage {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  min (sortedStopAt l (H+1) n ω) H

lemma horizonStage_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (l : List (Ω → ℝ≥0))
    (hl : ∀ τ ∈ l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (horizonStage l H n ω : WithTop ℝ≥0)) := by
  simpa only [horizonStage, WithTop.coe_min] using
    (sortedStopAt_stopping ℱ l hl (H+1) n).min_const H

lemma horizonStage_monotone {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H+1) (ω : Ω) :
    Monotone (fun n => horizonStage l H n ω) := by
  intro i j hij
  exact min_le_min_right H (sortedStopAt_monotone l (H+1) hl ω hij)

lemma horizonStage_le {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0) (n : ℕ) (ω : Ω) :
    horizonStage l H n ω ≤ H := min_le_right _ _

lemma horizonStage_last {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0) (ω : Ω) :
    horizonStage l H l.length ω = H := by
  simp only [horizonStage, sortedStopAt_length]
  exact min_eq_right (le_add_of_nonneg_right zero_le_one)

lemma exists_finite_stage (τ : ℕ → ℝ≥0) (N : ℕ) (t : ℝ≥0)
    (h0 : τ 0 ≤ t) (hN : t < τ N) :
    ∃ n < N, τ n ≤ t ∧ t < τ (n+1) := by
  induction N with
  | zero => exact False.elim ((not_lt_of_ge h0) hN)
  | succ N ih =>
    by_cases h : t < τ N
    · obtain ⟨n, hn, ht⟩ := ih h
      exact ⟨n, Nat.lt_trans hn (Nat.lt_succ_self N), ht⟩
    · exact ⟨N, Nat.lt_succ_self N, le_of_not_gt h, hN⟩

lemma horizonStage_zero {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H+1) (hzero : (fun _ : Ω => (0 : ℝ≥0)) ∈ l)
    (ω : Ω) : horizonStage l H 0 ω = 0 := by
  rw [horizonStage, sortedStopAt_zero l (H+1) hl hzero ω]
  exact min_eq_left bot_le

lemma horizonStage_cover {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H+1) (hzero : (fun _ : Ω => (0 : ℝ≥0)) ∈ l)
    (ω : Ω) (t : ℝ≥0) (ht : t < H) :
    ∃ n < l.length, horizonStage l H n ω ≤ t ∧ t < horizonStage l H (n+1) ω := by
  apply exists_finite_stage
  · rw [horizonStage_zero l H hl hzero ω]
    exact bot_le
  · rwa [horizonStage_last]

lemma horizonStage_nonempty {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (n : ℕ) (ω : Ω) (t : ℝ≥0)
    (hnt : horizonStage l H n ω ≤ t) (htn : t < horizonStage l H (n+1) ω) :
    sortedStopAt l (H+1) n ω ≤ t ∧ t < sortedStopAt l (H+1) (n+1) ω := by
  have htH : t < H := htn.trans_le (horizonStage_le l H (n+1) ω)
  have hnH : sortedStopAt l (H+1) n ω < H := by
    by_contra h
    have hn := le_of_not_gt h
    have he : horizonStage l H n ω = H := min_eq_right hn
    rw [he] at hnt
    exact (not_le_of_gt htH) hnt
  exact ⟨by simpa only [horizonStage, min_eq_left hnH.le] using hnt,
    htn.trans_le (min_le_left _ _)⟩

lemma phaseAt_const_horizon_interval {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H+1) (hρ : ∀ k, ρ k ∈ l)
    (n : ℕ) (ω : Ω) (t : ℝ≥0)
    (hnt : horizonStage l H n ω ≤ t) (htn : t < horizonStage l H (n+1) ω) :
    phaseAt ρ t ω = phaseAt ρ (horizonStage l H n ω) ω := by
  obtain ⟨hleft, hright⟩ := horizonStage_nonempty l H n ω t hnt htn
  have htH : t < H := htn.trans_le (horizonStage_le l H (n+1) ω)
  have hnH' : sortedStopAt l (H+1) n ω ≤ H := hleft.trans htH.le
  rw [horizonStage, min_eq_left hnH']
  exact phaseAt_const_sorted_interval ρ l (H+1) hl hρ n ω t hleft hright

lemma phaseAt_crossed_horizon_switch {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H+1) (hρ : ∀ k, ρ k ∈ l)
    (n : ℕ) (ω : Ω) (i : ι) (k : Fin 3)
    (hord : Monotone (fun j => ρ (i,j) ω))
    (hbefore : (phaseAt ρ (horizonStage l H n ω) ω i).val ≤ k.val)
    (hafter : k.val+1 ≤ (phaseAt ρ (horizonStage l H (n+1) ω) ω i).val) :
    ρ (i,k) ω = horizonStage l H (n+1) ω := by
  have hupper := (phaseAt_ge_iff ρ ω i hord _ k).mp hafter
  have hlt : horizonStage l H n ω < ρ (i,k) ω := by
    by_contra h
    have hc := (phaseAt_ge_iff ρ ω i hord _ k).mpr (le_of_not_gt h)
    omega
  have hsorted : sortedStopAt l (H+1) n ω < ρ (i,k) ω := by
    by_contra h
    have hp : ρ (i,k) ω ≤ sortedStopAt l (H+1) n ω := le_of_not_gt h
    have hH : ρ (i,k) ω ≤ H := hupper.trans (horizonStage_le l H (n+1) ω)
    exact (not_le_of_gt hlt) (le_min hp hH)
  have hnext := sortedStopAt_no_intermediate l (H+1) hl _ (hρ (i,k)) n ω hsorted
  exact le_antisymm hupper ((min_le_left _ _).trans hnext)

end SLEExactGauge.Multipoint

end

end OAI
