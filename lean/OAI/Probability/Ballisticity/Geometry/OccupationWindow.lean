import Mathlib
import OAI.Probability.Ballisticity.Geometry.RestrictedWindow
import OAI.Probability.Ballisticity.Stationary.ArrayClosed

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma typedCurrentArrayWindow_iterate_actual {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (j : ℤ) (m i : ℕ) (X : EpisodeInput e) :
    typedCurrentArrayWindow e j m (StationaryCompact.shift^[i] (actualArrayMap e t J X)) =
      actualCurrentWindow e t (j+i) m X := by
  have hc : ReferenceClasses.Consistent
      (currentOffsets e j (StationaryCompact.shift^[i] (actualArrayMap e t J X))) := by
    have h := congrArg (fun W : AmbientCurrentWindow e => W.1.1)
      (currentArrayWindow_iterate e j m i (actualArrayMap e t J X))
    change currentOffsets e j (StationaryCompact.shift^[i] (actualArrayMap e t J X)) =
      currentOffsets e (j+i) (actualArrayMap e t J X) at h
    rw [h]
    exact actual_currentOffsets e t J X (j+i)
  apply currentWindowInclude_injective e
  rw [currentWindowInclude_typed e j m _ hc,currentArrayWindow_iterate,currentArrayWindow_actual]

lemma rawCurrentOccupation_actual {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (filler : Environment d) (N m : ℕ) (M : Environment d → ℕ)
    (hact : ∀ (i : ℕ) ω, t ω i<N ↔ i<M ω) :
    (rawCurrentOccupation e ν Q (fun i ω => t ω i) (fun i => ht i) filler N m).map
      (rawCurrentProjection e) =
      (actualOccupationRaw e ν Q t J ht N M).map (typedCurrentArrayWindow e 0 m) := by
  rw [rawCurrentOccupation_projected e ν Q t ht hst filler N m]
  unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
  rw [Measure.map_finset_sum (typedCurrentArrayWindow_measurable e 0 m).aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  have hA : {X : EpisodeInput e | t X.1.1 i<N}={X | i<M X.1.1} := by
    ext X
    exact hact i X.1.1
  have hm : Measurable (fun X : EpisodeInput e => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  rw [hA,Measure.map_map (typedCurrentArrayWindow_measurable e 0 m) hm]
  congr 1
  funext X
  exact ((typedCurrentArrayWindow_iterate_actual e t J 0 m i X).trans (by simp)).symm

namespace Entropy
lemma normalize_map_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (μ : FiniteMeasure X) (f : X → Y) (hf : Measurable f)
    (hμ : μ≠0) :
    let ν : FiniteMeasure Y := ⟨(μ : Measure X).map f,inferInstance⟩
    (ν.normalize : Measure Y) = (μ.normalize : Measure X).map f := by
  let ν : FiniteMeasure Y := ⟨(μ : Measure X).map f,inferInstance⟩
  have hm : ν.mass=μ.mass := by
    change ((μ : Measure X).map f Set.univ).toNNReal = _
    rw [Measure.map_apply hf MeasurableSet.univ,Set.preimage_univ]
    rfl
  have hν : ν≠0 := by
    rw [← ν.mass_nonzero_iff,hm]
    exact μ.mass_nonzero_iff.mpr hμ
  change (ν.normalize : Measure Y)=_
  rw [ν.toMeasure_normalize_eq_of_nonzero hν,μ.toMeasure_normalize_eq_of_nonzero hμ,hm,
    Measure.map_smul _ hf.aemeasurable]
  rfl

lemma normalize_maps_equal {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (μ : FiniteMeasure X) (ν : FiniteMeasure Y) (f : X → Z) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) (hμ : μ≠0) (hν : ν≠0)
    (h : (μ : Measure X).map f = (ν : Measure Y).map g) :
    (μ.normalize : Measure X).map f = (ν.normalize : Measure Y).map g := by
  rw [←normalize_map_measure μ f hf hμ,←normalize_map_measure ν g hg hν]
  have he : (⟨(μ : Measure X).map f,inferInstance⟩ : FiniteMeasure Z) =
    ⟨(ν : Measure Y).map g,inferInstance⟩ := Subtype.ext h
  rw [he]

lemma real_mass_eq_of_maps_equal {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (f : X → Z) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) (h : μ.map f=ν.map g) :
    μ.real Set.univ=ν.real Set.univ := by
  have hh := congrArg (fun ρ : Measure Z => ρ.real Set.univ) h
  simpa only [Measure.real,Measure.map_apply hf MeasurableSet.univ,
    Measure.map_apply hg MeasurableSet.univ,Set.preimage_univ] using hh
end Entropy

end DirectionalTransience

end

end OAI
