import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.HistoryCompensator

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def PrefixCodegreeErrorExit {n : ℕ} (u v : Fin n)
    (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∃ j ≤ prefixTime n, 2*codegreeNoiseRadius n ≤
    |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1|

lemma codegreeNoiseRadius_tendsto_zero : Tendsto codegreeNoiseRadius atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (n : ℝ)^(-1/10000 : ℝ)) atTop (nhds 0)
  simpa only [Function.comp_def,neg_div] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/10000)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

lemma pmfMean_event_or_upper {α : Type*} [Fintype α] (μ : PMF α)
    (P Q A : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred A]
    (h : ∀ a, A a → P a ∨ Q a) :
    pmfMean μ (fun a => if A a then 1 else 0) ≤
      pmfMean μ (fun a => if P a then 1 else 0)+
        pmfMean μ (fun a => if Q a then 1 else 0) := by
  rw [← pmfMean_add]
  apply pmfMean_mono
  intro a _
  by_cases ha : A a
  · rw [ite_eq_left ha]
    rcases h a ha with hp | hq
    · rw [ite_eq_left hp]
      split <;> norm_num
    · rw [ite_eq_left hq]
      split <;> norm_num
  · rw [ite_eq_right ha]
    split <;> split <;> norm_num

lemma any_codegree_exit_noise_or_drift {n : ℕ}
    (hs : ∀ k ≤ prefixTime n, 0 < earlyTemplateScale 1 2 n k)
    (hr : codegreeNoiseRadius n ≤ 1/2)
    (ω : History (Graph n) (prefixTime n))
    (h : ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ PrefixCodegreeErrorExit uv.1 uv.2 ω) :
    (∃ uv : Fin n × Fin n, PrefixCodegreeNoiseExit uv.1 uv.2 ω) ∨
      (∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ PrefixCodegreeDriftExit uv.1 uv.2 ω) := by
  obtain ⟨uv,hne,hcross⟩ := h
  rcases codegree_first_exit_noise_or_drift uv.1 uv.2 hs hr ω hcross with hn | hd
  · exact Or.inl ⟨uv,hn⟩
  · exact Or.inr ⟨uv,hne,hd⟩

open Classical in

noncomputable def prefixCodegreeErrorProbability (n : ℕ) : ℝ :=
  pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
    (fun ω => if ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ PrefixCodegreeErrorExit uv.1 uv.2 ω then 1 else 0)

open Classical in

noncomputable def prefixCodegreeDriftProbability (n : ℕ) : ℝ :=
  pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
    (fun ω => if ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ PrefixCodegreeDriftExit uv.1 uv.2 ω then 1 else 0)

open Classical in

noncomputable def prefixCodegreeNoiseProbability (n : ℕ) : ℝ :=
  pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
    (fun ω => if ∃ uv : Fin n × Fin n, PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0)

lemma prefix_codegree_error_probability_split (n : ℕ)
    (hs : ∀ k ≤ prefixTime n, 0 < earlyTemplateScale 1 2 n k)
    (hr : codegreeNoiseRadius n ≤ 1/2) :
    prefixCodegreeErrorProbability n ≤ prefixCodegreeNoiseProbability n+prefixCodegreeDriftProbability n := by
  classical
  unfold prefixCodegreeErrorProbability prefixCodegreeNoiseProbability prefixCodegreeDriftProbability
  have hm := pmfMean_event_or_upper
    (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
    (fun ω => ∃ uv : Fin n × Fin n, PrefixCodegreeNoiseExit uv.1 uv.2 ω)
    (fun ω => ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ PrefixCodegreeDriftExit uv.1 uv.2 ω)
    (fun ω => ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ PrefixCodegreeErrorExit uv.1 uv.2 ω)
    (any_codegree_exit_noise_or_drift hs hr)
  convert hm using 1

lemma prefix_codegree_noise_probability_bound : ∀ᶠ n : ℕ in atTop,
    prefixCodegreeNoiseProbability n ≤ Real.exp (-(Real.log n)^(4/3 : ℝ)) := by
  filter_upwards [all_codegree_stopped_noise_envelope] with n hn
  unfold prefixCodegreeNoiseProbability
  exact hn

theorem prefix_codegree_error_probability_reduction : ∀ᶠ n : ℕ in atTop,
    prefixCodegreeErrorProbability n ≤ Real.exp (-(Real.log n)^(4/3 : ℝ))+
      prefixCodegreeDriftProbability n := by
  filter_upwards [prefix_codegree_noise_probability_bound,earlyTemplateScale_regular 1 2,
    codegreeNoiseRadius_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))]
    with n hnoise hscale hr
  have hs : prefixCodegreeErrorProbability n ≤
      prefixCodegreeNoiseProbability n+prefixCodegreeDriftProbability n :=
    prefix_codegree_error_probability_split n hscale.1 hr.le
  calc
    prefixCodegreeErrorProbability n ≤
        prefixCodegreeNoiseProbability n+prefixCodegreeDriftProbability n := hs
    _ ≤ Real.exp (-(Real.log n)^(4/3 : ℝ))+prefixCodegreeDriftProbability n :=
      add_le_add hnoise (le_refl (prefixCodegreeDriftProbability n))

end SharpTerminalLeave

end

end OAI
