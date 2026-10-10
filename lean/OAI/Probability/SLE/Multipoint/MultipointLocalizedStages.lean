import OAI.Probability.SLE.Multipoint.MultipointHorizonStages

namespace OAI

/-! Stop the integration at a bounded random localization time, while
continuing to detect phases from the original radius switches. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def localizedStage {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  min (sortedStopAt l (H+1) n ω) (χ ω)

lemma localizedStage_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (l : List (Ω → ℝ≥0))
    (hl : ∀ τ ∈ l, IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (χ : Ω → ℝ≥0)
    (hχ : IsStoppingTime ℱ (fun ω => (χ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (localizedStage l H χ n ω : WithTop ℝ≥0)) := by
  simpa only [localizedStage, WithTop.coe_min] using
    (sortedStopAt_stopping ℱ l hl (H+1) n).min hχ

lemma localizedStage_monotone {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H+1) (ω : Ω) :
    Monotone (fun n => localizedStage l H χ n ω) := by
  intro i j hij
  exact min_le_min_right (χ ω) (sortedStopAt_monotone l (H+1) hl ω hij)

lemma localizedStage_le {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : localizedStage l H χ n ω ≤ χ ω :=
  min_le_right _ _

lemma localizedStage_last {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (hχ : ∀ ω, χ ω ≤ H) (ω : Ω) :
    localizedStage l H χ l.length ω = χ ω := by
  simp only [localizedStage, sortedStopAt_length]
  exact min_eq_right ((hχ ω).trans (le_add_of_nonneg_right zero_le_one))

lemma localizedStage_zero {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (hl : ∀ τ ∈ l, ∀ ω, τ ω ≤ H+1)
    (hzero : (fun _ : Ω => (0 : ℝ≥0)) ∈ l) (ω : Ω) :
    localizedStage l H χ 0 ω = 0 := by
  rw [localizedStage, sortedStopAt_zero l (H+1) hl hzero ω]
  exact min_eq_left bot_le

lemma localizedStage_nonempty {Ω : Type*} (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) (t : ℝ≥0)
    (hnt : localizedStage l H χ n ω ≤ t) (htn : t < localizedStage l H χ (n+1) ω) :
    sortedStopAt l (H+1) n ω ≤ t ∧ t < sortedStopAt l (H+1) (n+1) ω := by
  have htχ : t < χ ω := htn.trans_le (localizedStage_le l H χ (n+1) ω)
  have hnχ : sortedStopAt l (H+1) n ω < χ ω := by
    by_contra h
    have he : localizedStage l H χ n ω = χ ω := min_eq_right (le_of_not_gt h)
    rw [he] at hnt
    exact (not_le_of_gt htχ) hnt
  exact ⟨by simpa only [localizedStage, min_eq_left hnχ.le] using hnt,
    htn.trans_le (min_le_left _ _)⟩

lemma phaseAt_const_localized_interval {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H+1) (hρ : ∀ k, ρ k ∈ l)
    (n : ℕ) (ω : Ω) (t : ℝ≥0)
    (hnt : localizedStage l H χ n ω ≤ t) (htn : t < localizedStage l H χ (n+1) ω) :
    phaseAt ρ t ω = phaseAt ρ (localizedStage l H χ n ω) ω := by
  obtain ⟨hleft, hright⟩ := localizedStage_nonempty l H χ n ω t hnt htn
  have hnχ : sortedStopAt l (H+1) n ω ≤ χ ω :=
    hleft.trans ((htn.trans_le (localizedStage_le l H χ (n+1) ω)).le)
  rw [localizedStage, min_eq_left hnχ]
  exact phaseAt_const_sorted_interval ρ l (H+1) hl hρ n ω t hleft hright

lemma phaseAt_crossed_localized_switch {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (χ : Ω → ℝ≥0) (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H+1) (hρ : ∀ k, ρ k ∈ l)
    (n : ℕ) (ω : Ω) (i : ι) (k : Fin 3)
    (hord : Monotone (fun j => ρ (i,j) ω))
    (hbefore : (phaseAt ρ (localizedStage l H χ n ω) ω i).val ≤ k.val)
    (hafter : k.val+1 ≤ (phaseAt ρ (localizedStage l H χ (n+1) ω) ω i).val) :
    ρ (i,k) ω = localizedStage l H χ (n+1) ω := by
  have hupper := (phaseAt_ge_iff ρ ω i hord _ k).mp hafter
  have hlt : localizedStage l H χ n ω < ρ (i,k) ω := by
    by_contra h
    have hc := (phaseAt_ge_iff ρ ω i hord _ k).mpr (le_of_not_gt h)
    omega
  have hsorted : sortedStopAt l (H+1) n ω < ρ (i,k) ω := by
    by_contra h
    have hp : ρ (i,k) ω ≤ sortedStopAt l (H+1) n ω := le_of_not_gt h
    have hχ : ρ (i,k) ω ≤ χ ω := hupper.trans (localizedStage_le l H χ (n+1) ω)
    exact (not_le_of_gt hlt) (le_min hp hχ)
  have hnext := sortedStopAt_no_intermediate l (H+1) hl _ (hρ (i,k)) n ω hsorted
  exact le_antisymm hupper ((min_le_left _ _).trans hnext)

end SLEExactGauge.Multipoint

end

end OAI
