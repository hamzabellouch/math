import Mathlib
import OAI.Probability.Ballisticity.Stationary.BadCrossingEpisodes

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma arrayMark_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (r : ℕ) (i : ℤ) : (StationaryCompact.shift^[r] Y).1 i = Y.1 (i+r) := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change (StationaryCompact.shift^[r] Y).1 (i+1)=_
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm (1:ℤ)]

noncomputable def cutENNReal (B : ℝ≥0) : C(ℝ≥0∞,ℝ) :=
  ⟨fun x => (min x (B:ℝ≥0∞)).toReal, by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hf : min x (B:ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    exact (ENNReal.continuousAt_toReal hf).comp (f:=fun y : ℝ≥0∞ => min y (B:ℝ≥0∞))
      (show ContinuousAt (fun y : ℝ≥0∞ => min y (B:ℝ≥0∞)) x from
        (continuous_id.min continuous_const).continuousAt)⟩

lemma cutENNReal_nonneg (B : ℝ≥0) (x : ℝ≥0∞) : 0 ≤ cutENNReal B x := ENNReal.toReal_nonneg
lemma cutENNReal_le (B : ℝ≥0) (x : ℝ≥0∞) : cutENNReal B x ≤ B := by
  change (min x (B:ℝ≥0∞)).toReal ≤ (B:ℝ≥0∞).toReal
  exact ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right _ _)

noncomputable def stageMarkCut {d : ℕ} (e : Direction d) (B : ℝ≥0)
    (i : ℤ) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal B).comp ⟨fun Y => ((Y.1 i).2.1).toENNReal,
    ENat.continuous_toENNReal.comp (by fun_prop)⟩

noncomputable def dropMarkCut {d : ℕ} (e : Direction d) (B : ℝ≥0)
    (i : ℤ) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal B).comp ⟨fun Y => (Y.1 i).2.2,by fun_prop⟩

lemma actualOccupationRaw_env_test {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (F : C(ActualEpisodeArray e,ℝ)) (G : ℕ → Environment d → ℝ)
    (hG : ∀ i, Measurable (G i))
    (hFG : ∀ i X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))=G i X.1.1) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=
      ∑ i∈Finset.range N, ∫ ω in {ω | i<M ω}, G i ω ∂Q := by
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hFG]
  exact episodeInputLaw_env_integral e ν (Q.restrict {ω | i<M ω}) t ht (G i) (hG i)

end DirectionalTransience

end

end OAI
