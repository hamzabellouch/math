import Mathlib
import OAI.Probability.Ballisticity.Estimates.OperationalLengthMarks
import OAI.Probability.Ballisticity.Stationary.ArrayMarkTests
import OAI.Probability.Ballisticity.Stationary.BadArraySampling

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def lengthUnitTest {d : ℕ} (e : Direction d) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal 1).comp ⟨fun Y => ((Y.1 0).1).toENNReal,
    ENat.continuous_toENNReal.comp (by fun_prop)⟩

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma raw_lengthUnit (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    (∫ Y, lengthUnitTest e Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N) N (C.activeCount hef N)) =
    (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
      (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ := by
  let T := episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
  have hm (i : ℕ) : Measurable (fun ω => (min (T ω (i+1)-T ω i) 1:ℕ)) :=
    ((episodeBoundary_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N (i+1)).sub
      (episodeBoundary_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i)).min measurable_const
  rw [actualOccupationRaw_env_test e ν Q _ _ _ (C.paddedStages_measurable hef N) N _
    (C.activeCount_measurable hef N) (lengthUnitTest e)
    (fun i ω => (min (T ω (i+1)-T ω i) 1:ℕ))
    (fun i => (measurable_of_countable (fun n:ℕ => (n:ℝ))).comp (hm i))
    (fun i X => by
      change (min (((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
        (C.paddedStages hef N) X)).1 0).1).toENNReal (1:ℝ≥0∞)).toReal = _
      rw [C.actual_lengthMark]
      change (min ((T X.1.1 (i+1)-T X.1.1 i:ℕ):ℝ≥0∞) 1).toReal = _
      generalize T X.1.1 (i+1)-T X.1.1 i = n
      simp only [ENNReal.toReal_min (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
        ENNReal.toReal_natCast,ENNReal.toReal_one,Nat.cast_min,Nat.cast_one]),
    actualOccupationRaw_mass e ν Q _ _ _ (C.paddedStages_measurable hef N) N _ (C.activeCount_measurable hef N)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∫ ω in {ω | i<C.activeCount hef N ω}, ((min (T ω (i+1)-T ω i) 1:ℕ):ℝ) ∂Q) =
      ∫ ω in {ω | i<C.activeCount hef N ω}, (1:ℝ) ∂Q := by
      apply setIntegral_congr_fun (measurableSet_lt measurable_const (C.activeCount_measurable hef N))
      intro ω hω
      have ha : T ω i<N := (EpisodeChainLedger.active_iff_lt_number (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i).mpr hω
      have hh := episodeFinal_gt (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N (T ω i) ω
      have hp : T ω i<T ω (i+1) := by
        change T ω i < if T ω i<N then _ else _
        rw [ite_eq_left ha]
        exact hh
      have hmin : min (T ω (i+1)-T ω i) 1=1 := by omega
      simp only [hmin,Nat.cast_one]
    _ = _ := by simp

lemma bad_limit_positive_length (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), 0<(Y.1 0).1 := by
  have he (n : ℕ) : (∫ Y, lengthUnitTest e Y ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]):Measure (ActualEpisodeArray e)))=1 := by
    change (∫ Y, lengthUnitTest e Y ∂(actualOccupation e ν _ _ _ _ _ _:Measure _))=1
    rw [actualOccupation_integral e ν _ _ _ _ _ _ (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)),C.raw_lengthUnit]
    exact inv_mul_cancel₀ (ne_of_gt (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)))
  have hconv := (ProbabilityMeasure.continuous_integral_continuousMap (lengthUnitTest e)).continuousAt.tendsto.comp hlim
  have hl : Tendsto (fun n => ∫ Y, lengthUnitTest e Y ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]):Measure (ActualEpisodeArray e))) atTop (𝓝 (1:ℝ)) := by
    simp_rw [he]
    exact tendsto_const_nhds
  have hi : (∫ Y, lengthUnitTest e Y ∂(ρ:Measure (ActualEpisodeArray e)))=1 :=
    tendsto_nhds_unique hconv hl
  have hz : (∫ Y, 1-lengthUnitTest e Y ∂(ρ:Measure (ActualEpisodeArray e)))=0 := by
    rw [integral_sub (integrable_const _)
      ((lengthUnitTest e).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const,probReal_univ,one_smul,hi,sub_self]
  have hnon (Y : ActualEpisodeArray e) : 0≤1-lengthUnitTest e Y := by
    exact sub_nonneg.mpr (cutENNReal_le 1 _)
  have hae := (integral_eq_zero_iff_of_nonneg hnon
    ((1-lengthUnitTest e).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hz
  filter_upwards [hae] with Y hY
  by_contra hh
  have hh : (Y.1 0).1=0 := le_antisymm (le_of_not_gt hh) bot_le
  have htest : lengthUnitTest e Y=0 := by simp [lengthUnitTest,cutENNReal,hh]
  rw [htest] at hY
  norm_num at hY

end OperationalConstants
end DirectionalTransience

end

end OAI
