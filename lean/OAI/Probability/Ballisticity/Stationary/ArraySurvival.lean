import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayWindowMarks
import OAI.Probability.Ballisticity.Estimates.BoundedAnchorAverage

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arraySurvivalSum {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ∑ a∈Finset.range n, upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ

lemma arraySurvivalSum_lowerSemicontinuous {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ) :
    LowerSemicontinuous (arraySurvivalSum e i m H n) := by
  apply lowerSemicontinuous_sum
  intro a ha
  exact (upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).comp
    (arrayUpperRows_continuous e i m a)

noncomputable def arraySurvivalThreshold {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ)
    (ε : ℝ) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ENNReal.ofReal ((n:ℝ)*((expNeg (arrayWindowCost e i m Y)).toReal+ε))

lemma arraySurvivalThreshold_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ) :
    Continuous (arraySurvivalThreshold e i m n ε) :=
  ENNReal.continuous_ofReal.comp (continuous_const.mul
    ((expNeg_toReal_continuous.comp (arrayWindowCost_continuous e i m)).add continuous_const))

def survivalViolation {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ) :
    Set (ActualEpisodeArray e) :=
  {Y | ∃ H : ℕ, arrayWindowHeight e i m Y=H ∧
    arraySurvivalThreshold e i m n ε Y<arraySurvivalSum e i m H n Y}

lemma survivalViolation_open {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ) :
    IsOpen (survivalViolation e i m n ε) := by
  simp only [survivalViolation,Set.ofPred_exists]
  apply isOpen_iUnion
  intro H
  have he : IsOpen {Y : ActualEpisodeArray e | arrayWindowHeight e i m Y=(H:ℕ∞)} :=
    (ENat.isOpen_singleton (by simp)).preimage (arrayWindowHeight_continuous e i m)
  have hc : IsClosed {Y : ActualEpisodeArray e | arraySurvivalSum e i m H n Y ≤
      arraySurvivalThreshold e i m n ε Y} :=
    (arraySurvivalSum_lowerSemicontinuous e i m H n).isClosed_epigraph.preimage
      (continuous_id.prodMk (arraySurvivalThreshold_continuous e i m n ε))
  simpa only [Set.compl_ofPred,not_le,Set.ofPred_and] using he.inter hc.isOpen_compl

noncomputable def localSurvival {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (z : HorizontalSpace e) : ℝ≥0∞ :=
  variableHitKernel (realPosition (step e)) H (ω,horizontalLift e k z) Set.univ

lemma localSurvival_le_one {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (z : HorizontalSpace e) : localSurvival e ω k H z ≤ 1 := by
  change hitKernel (Strip (realPosition (step e)) (horizontalLift e k z) H)
    (Upper (realPosition (step e)) (horizontalLift e k z) H) (ω,horizontalLift e k z) Set.univ ≤ 1
  exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _
lemma localSurvival_ne_top {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (z : HorizontalSpace e) : localSurvival e ω k H z≠⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (localSurvival_le_one e ω k H z)

lemma actual_arraySurvivalSum {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (i : ℤ) (m n : ℕ) :
    arraySurvivalSum e i m (t X.1.1 (i+m)-t X.1.1 i) n (actualArrayMap e t J X)=
      ENNReal.ofReal (∑ a∈Finset.range n, (localSurvival e X.1.1 (t X.1.1 i)
        (t X.1.1 (i+m)-t X.1.1 i) (X.1.2 (i,a))).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [ENNReal.ofReal_toReal (localSurvival_ne_top _ _ _ _ _)]
  change upperHorizontalKernel e _ (fun p => episodeSplicedRow e t X i m a p.1 p.2) 0 Set.univ=_
  rw [episodeSpliced_kernel]
  simp only [Set.mem_univ,Set.ofPred_true,add_zero,localSurvival]

lemma localSurvival_mean {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) :
    (∫ z, (localSurvival e ω k H z).toReal ∂globalHorizontalProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 ((k+H:ℕ):ℝ) ω /
        crossingQuenched (realPosition (step e)) 0 k ω).toReal := by
  rw [integral_toReal (measurable_of_countable _).aemeasurable
    (Eventually.of_forall (fun z => lt_top_iff_ne_top.mpr (localSurvival_ne_top _ _ _ _ z)))]
  apply ENNReal.toReal_mono (ENNReal.div_ne_top (crossingQuenched_ne_top _ _ _ _) hk)
  have hh := globalHorizontalProfile_continuation e k H ω hk Set.univ
  simpa only [localSurvival,Set.preimage_univ,measure_univ,mul_one,Nat.cast_add] using hh

lemma actual_survivalViolation_iff {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0)
    (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    actualArrayMap e t J X∈survivalViolation e i m n ε ↔
      (crossingQuenched (realPosition (step e)) 0 (t X.1.1 (i+m)) X.1.1 /
        crossingQuenched (realPosition (step e)) 0 (t X.1.1 i) X.1.1).toReal+ε <
      sampleAverage (fun a E => (localSurvival e X.1.1 (t X.1.1 i)
        (t X.1.1 (i+m)-t X.1.1 i) (E (i,a))).toReal) n X.1.2 := by
  have hik := hmono (show i ≤ i+(m:ℤ) by omega)
  simp only [survivalViolation,Set.mem_ofPred_eq,arrayWindowHeight_actual e t J X hmono,
    Nat.cast_inj,exists_eq_left',actual_arraySurvivalSum]
  unfold arraySurvivalThreshold
  rw [arrayWindowCost_actual e t J X hmono hpos,expNeg_log_ratio _ _ (hpos _)
    (crossingQuenched_ne_top _ _ _ _) (hpos _) (crossingQuenched_ne_top _ _ _ _)
    (crossingQuenched_antitone _ _ _ (by exact_mod_cast hik)),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
  unfold sampleAverage
  rw [show (n:ℝ)⁻¹*∑ a∈Finset.range n, _ = (∑ a∈Finset.range n, _)/(n:ℝ) by ring,
    lt_div_iff₀ (by exact_mod_cast hn)]
  rw [mul_comm]

end DirectionalTransience

end

end OAI
