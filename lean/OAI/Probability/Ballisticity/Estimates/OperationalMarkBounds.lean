import Mathlib
import OAI.Probability.Ballisticity.Estimates.BadOccupationLimit
import OAI.Probability.Ballisticity.Stationary.ArrayMarkTests

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma stagesAt_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) : Measurable (fun ω => C.stagesAt hef N ω i) :=
  EpisodeChainLedger.stepMark_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

lemma stagesAt_integrable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    Integrable (fun ω => (C.stagesAt hef N ω i:ℝ)) Q := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun n:ℕ => (n:ℝ))).comp (C.stagesAt_measurable hef N i)).aestronglyMeasurable) N
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  change (C.stagesAt hef N ω i:ℝ) ≤ (N:ℝ)
  apply Nat.cast_le.mpr
  exact EpisodeChainLedger.stepMark_le (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

lemma actual_stageMark (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (X : EpisodeInput e) :
    ((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).2.1 = (C.stagesAt hef N X.1.1 i:ℕ∞) := by
  rw [arrayMark_iterate]
  simp only [zero_add,actualArrayMap,paddedStages,EpisodeChainLedger.arrayStages,
    Int.natCast_nonneg,not_lt.mpr,ite_false,Int.toNat_natCast,stagesAt]

lemma stageMarkCut_actual (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (B : ℝ≥0) (X : EpisodeInput e) :
    stageMarkCut e B 0 (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)) = min (C.stagesAt hef N X.1.1 i:ℝ) B := by
  change (min (((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).2.1).toENNReal (B:ℝ≥0∞)).toReal = _
  rw [C.actual_stageMark]
  simp only [ENat.toENNReal_coe]
  rw [ENNReal.toReal_min (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top]
  simp

variable [IsProbabilityMeasure ν]

lemma raw_stageMark_bound (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] (B : ℝ≥0) :
    (∫ Y, stageMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)) ≤
      ∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q := by
  rw [actualOccupationRaw_env_test e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.activeCount_measurable hef N) (stageMarkCut e B 0)
    (fun i ω => min (C.stagesAt hef N ω i:ℝ) B)
    (fun i => (((measurable_of_countable (fun n:ℕ => (n:ℝ))).comp (C.stagesAt_measurable hef N i)).min measurable_const))
    (fun i X => C.stageMarkCut_actual hef N i B X)]
  have hsum : (∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q) =
      ∑ i∈Finset.range N, ∫ ω, (C.stagesAt hef N ω i:ℝ) ∂Q := by
    rw [←integral_finsetSum (Finset.range N) (fun i _ => C.stagesAt_integrable hef N i Q)]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp only [stagesAt]
    exact_mod_cast (EpisodeChainLedger.stepMark_sum (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N).symm
  rw [hsum]
  apply Finset.sum_le_sum
  intro i _
  apply (integral_mono ((C.stagesAt_integrable hef N i Q).inf (integrable_const _)).integrableOn
    (C.stagesAt_integrable hef N i Q).integrableOn (fun _ => min_le_left _ _)).trans
  exact setIntegral_le_integral (C.stagesAt_integrable hef N i Q)
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma dropAt_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) : Measurable (fun ω => C.dropAt hef N ω i) :=
  EpisodeChainLedger.dropMark_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

lemma dropAt_bounds (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (ω : Environment d) (hω : ∀ y u, C.κ ≤ (ω y).1 u) :
    0 ≤ C.dropAt hef N ω i ∧ C.dropAt hef N ω i ≤ C.injectionCost+2*C.b*C.stagesAt hef N ω i := by
  have hh := EpisodeChainLedger.dropMark_bounds_local (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N C.order C.hf.le C.hb.le
    (lt_of_lt_of_le zero_lt_one C.hs) C.height_pos C.κ C.hκ0 C.hκ1
    (lt_of_lt_of_le (by norm_num) C.hk) C.hbκ ω hω i
  refine ⟨hh.1,hh.2.trans ?_⟩
  change C.injectionCost*(if _ then 1 else 0)+_ ≤ _
  split <;> simp only [mul_one,mul_zero,zero_add]
  · rfl
  · change 2*C.b*(C.stagesAt hef N ω i:ℝ) ≤ C.injectionCost+2*C.b*C.stagesAt hef N ω i
    linarith [C.cost_nonneg]

lemma dropAt_integrable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u) : Integrable (fun ω => C.dropAt hef N ω i) Q :=
  EpisodeChainLedger.dropMark_integrable_local (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N C.order C.hf.le C.hb.le
    (lt_of_lt_of_le zero_lt_one C.hs) C.height_pos C.κ C.hκ0 C.hκ1
    (lt_of_lt_of_le (by norm_num) C.hk) C.hbκ Q hQ i

lemma actual_dropMark (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (X : EpisodeInput e) :
    ((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).2.2 = ENNReal.ofReal (C.dropAt hef N X.1.1 i) := by
  rw [arrayMark_iterate]
  simp only [zero_add,actualArrayMap,episodeCost,paddedTimes,EpisodeChainLedger.arrayTime,
    Int.toNat_natCast,show (i:ℤ)+1=((i+1:ℕ):ℤ) by omega,dropAt, EpisodeChainLedger.dropMark]

lemma dropCut_actual (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (B : ℝ≥0) (X : EpisodeInput e) :
    dropMarkCut e B 0 (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)) = cutENNReal B (ENNReal.ofReal (C.dropAt hef N X.1.1 i)) := by
  exact congrArg (cutENNReal B) (C.actual_dropMark hef N i X)

lemma cut_ofReal_eq_min (B : ℝ≥0) (x : ℝ) (hx : 0≤x) :
    cutENNReal B (ENNReal.ofReal x)=min x B := by
  change (min (ENNReal.ofReal x) (B:ℝ≥0∞)).toReal=_
  rw [ENNReal.toReal_min ENNReal.ofReal_ne_top ENNReal.coe_ne_top,ENNReal.toReal_ofReal hx]
  rfl

end OperationalConstants
end DirectionalTransience

end

end OAI
