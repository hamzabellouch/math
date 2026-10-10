import Mathlib
import OAI.Probability.Ballisticity.Estimates.SurvivalConditional

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma survivalViolation_weak_bound {d : ℕ} (e : Direction d)
    (μ : ℕ → ProbabilityMeasure (ActualEpisodeArray e)) (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto μ atTop (𝓝 ρ)) (i : ℤ) (m n : ℕ) (ε : ℝ) (c : ℝ≥0∞)
    (hμ : ∀ k, (μ k : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε)≤c) :
    (ρ : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε)≤c := by
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (survivalViolation_open e i m n ε)).trans
  exact (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hμ))

noncomputable def arraySurvivalAverage {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e) : ℝ := (n:ℝ)⁻¹*(arraySurvivalSum e i m H n Y).toReal

lemma arraySurvivalAverage_nonneg {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e) : 0≤arraySurvivalAverage e i m H n Y := by
  unfold arraySurvivalAverage
  positivity

lemma arraySurvivalAverage_le_of_notMem {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (hn : 0<n) (ε : ℝ) (hε : 0≤ε) (Y : ActualEpisodeArray e)
    (hH : arrayWindowHeight e i m Y=H) (hnot : Y∉survivalViolation e i m n ε) :
    arraySurvivalAverage e i m H n Y≤(expNeg (arrayWindowCost e i m Y)).toReal+ε := by
  have hs : arraySurvivalSum e i m H n Y ≤ arraySurvivalThreshold e i m n ε Y := by
    by_contra h
    exact hnot ⟨H,hH,not_le.mp h⟩
  have hh := ENNReal.toReal_mono (show arraySurvivalThreshold e i m n ε Y≠⊤ from ENNReal.ofReal_ne_top) hs
  rw [arraySurvivalThreshold,ENNReal.toReal_ofReal (by positivity)] at hh
  unfold arraySurvivalAverage
  calc
    _ ≤ (n:ℝ)⁻¹*((n:ℝ)*((expNeg (arrayWindowCost e i m Y)).toReal+ε)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hn.ne'),one_mul]

def ArrayAveragedSurvival {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  ∀ (i : ℤ) (m H : ℕ), arrayWindowHeight e i m Y=H →
    limsup (fun r : ℕ => arraySurvivalAverage e i m H (2^r) Y) atTop ≤
      (expNeg (arrayWindowCost e i m Y)).toReal

lemma arrayAveragedSurvival_of_bounds {d : ℕ} (e : Direction d)
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hb : ∀ (i : ℤ) (m n : ℕ), 0<n → ∀ ε : ℝ, 0<ε →
      (ρ : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε) ≤ ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayAveragedSurvival e Y := by
  have hbc (i : ℤ) (m k : ℕ) : ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
      ∀ᶠ r : ℕ in atTop, Y∉survivalViolation e i m (2^r) (1/(k+1:ℝ)) := by
    apply ae_eventually_notMem
    have hs : Summable (fun r : ℕ => ((2^r:ℕ):ℝ)⁻¹/(1/(k+1:ℝ))^2) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat,←inv_pow] using
        (summable_geometric_of_norm_lt_one (show ‖(2:ℝ)⁻¹‖<1 by norm_num)).div_const ((1/(k+1:ℝ))^2)
    exact ne_top_of_le_ne_top hs.tsum_ofReal_lt_top.ne
      (ENNReal.tsum_le_tsum (fun r => hb i m (2^r) (by positivity) _ (by positivity)))
  have hall : ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ (i : ℤ) (m k : ℕ),
      ∀ᶠ r : ℕ in atTop, Y∉survivalViolation e i m (2^r) (1/(k+1:ℝ)) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => hbc i m k
  filter_upwards [hall] with Y hY
  intro i m H hH
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun r => arraySurvivalAverage_nonneg e i m H (2^r) Y))
  filter_upwards [hY i m k] with r hr
  exact (arraySurvivalAverage_le_of_notMem e i m H (2^r) (by positivity) _ (by positivity) Y hH hr).trans
    (add_le_add_right hk.le _)

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_averaged_survival (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayAveragedSurvival e Y := by
  apply arrayAveragedSurvival_of_bounds e ρ
  intro i m n hn ε hε
  apply survivalViolation_weak_bound e _ ρ hlim i m n ε _
  intro k
  apply actualOccupation_survivalViolation_bound e ν _
    (C.paddedTimes hef (Ns k)) (C.paddedStages hef (Ns k))
    (C.paddedTimes_measurable hef (Ns k)) (C.paddedStages_measurable hef (Ns k)) (Ns k)
    (C.activeCount hef (Ns k)) (C.activeCount_measurable hef (Ns k))
    (C.bad_raw_mass_pos hef (Ns k) (hN k) (hmass k)) _ i m n hn ε hε
  have hQ := (cond_absolutelyContinuous (μ:=environmentLaw ν)
    (s:=badCrossingEvent e (Ns k) (1/2))).ae_le C.rows
  filter_upwards [hQ] with ω hω
  refine ⟨C.paddedTimes_int_mono hef (Ns k) ω,?_⟩
  intro H
  exact ne_of_gt ((ENNReal.pow_pos (show (0:ℝ≥0∞)<C.κ by exact_mod_cast C.hκ0) H).trans_le
    (coordinate_survival_lower e ω C.κ (fun y => hω y e) H))

end OperationalConstants
end DirectionalTransience

end

end OAI
