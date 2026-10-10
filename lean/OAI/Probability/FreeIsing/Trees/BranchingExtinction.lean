import OAI.Probability.FreeIsing.Critical.Branching
import OAI.Probability.FreeIsing.Trees.BranchingSurvivalLaw

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.BranchingSurvival

theorem probability_eq_survival (b : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) : probability b p n = CriticalBranching.survival b p n := by
  induction n with
  | zero => simp [CriticalBranching.survival]
  | succ n ih =>
      rw [probability_succ b hp0 hp1, ih]
      rfl

theorem probability_le_reciprocal {b : ℕ} (hb : 1 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) (n : ℕ) :
    probability b p n ≤ 1 / (1 + (((b : ℝ) - 1) * p ^ 2) * n) := by
  rw [probability_eq_survival b hp.1 hp.2]
  exact CriticalBranching.survival_le_reciprocal hb hp hcritical n

theorem probability_tendsto_zero {b : ℕ} (hb : 2 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) :
    Tendsto (probability b p) atTop (𝓝 0) := by
  have heq : probability b p = CriticalBranching.survival b p :=
    funext (probability_eq_survival b hp.1 hp.2)
  rw [heq]
  exact CriticalBranching.survival_tendsto_zero hb hp hcritical

lemma survives_succ_subset (b : ℕ) (p : ℝ) (n : ℕ) :
    @survives b p (n + 1) ⊆ survives p n := by
  induction n with
  | zero => exact Set.subset_univ _
  | succ n ih =>
      rintro U ⟨i, hi, hchild⟩
      exact ⟨i, hi, ih hchild⟩

lemma antitone_survives (b : ℕ) (p : ℝ) : Antitone (@survives b p) :=
  antitone_nat_of_succ_le (survives_succ_subset b p)

theorem measure_survives_forever {b : ℕ} (hb : 2 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) :
    wordMeasure b (⋂ n : ℕ, survives p n) = 0 := by
  have hlim : Tendsto (fun n => wordMeasure b (survives p n)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp
      (probability_tendsto_zero hb hp hcritical)
    simpa [Function.comp_def, probability, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hcontinuity := tendsto_measure_iInter_atTop
    (fun n => (measurableSet_survives b p n).nullMeasurableSet)
    (antitone_survives b p) (show ∃ n, wordMeasure b (survives p n) ≠ ⊤ from
      ⟨0, measure_ne_top _ _⟩)
  exact tendsto_nhds_unique hcontinuity hlim

theorem ae_exists_extinction_depth {b : ℕ} (hb : 2 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) :
    ∀ᵐ U ∂wordMeasure b, ∃ n : ℕ, U ∉ survives p n := by
  apply ae_iff.mpr
  have hs : {U : Labels b | ¬ ∃ n : ℕ, U ∉ survives p n} =
      ⋂ n : ℕ, survives p n := by
    ext U
    simp
  rw [hs]
  exact measure_survives_forever hb hp hcritical

theorem measurePreserving_wordShift (b : ℕ) (w : List (Fin b)) :
    MeasurePreserving (fun U : Labels b => fun v => U (w ++ v))
      (wordMeasure b) (wordMeasure b) := by
  refine ⟨by fun_prop, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj
    (fun x y h => List.append_cancel_left h)

theorem ae_all_extinction_depth {b : ℕ} (hb : 2 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) :
    ∀ᵐ U ∂wordMeasure b, ∀ w : List (Fin b),
      ∃ n : ℕ, (fun v => U (w ++ v)) ∉ survives p n := by
  apply ae_all_iff.mpr
  intro w
  exact (measurePreserving_wordShift b w).quasiMeasurePreserving.ae
    (ae_exists_extinction_depth hb hp hcritical)

end Problem367.BranchingSurvival

end

end OAI
