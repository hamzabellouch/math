import Mathlib
import OAI.Probability.Ballisticity.Geometry.OccupationWindow

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def actualCurrentLaw {d : ℕ} (e : Direction d) (m : ℕ)
    (L : ProbabilityMeasure (ActualEpisodeArray e)) : ProbabilityMeasure (CurrentWindow e) :=
  L.map (typedCurrentArrayWindow e 0 m)

lemma finiteMeasure_ne_zero_of_real_mass_pos {X : Type*} [MeasurableSpace X]
    (μ : FiniteMeasure X) (h : 0<(μ : Measure X).real Set.univ) : μ≠0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem actualOccupation_window_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν)≠∞)
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (hmono : ∀ ω, Monotone (fun i : ℕ => t ω i))
    (N m : ℕ) (M : Environment d → ℕ)
    (hact : ∀ (i : ℕ) ω, t ω i<N ↔ i<M ω)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    let W := (actualCurrentLaw e m (actualOccupation e ν Q t J ht N M) : Measure (CurrentWindow e))
    klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (actualOccupationRaw e ν Q t J ht N M).real Set.univ) := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  have : Nonempty (ReferenceClasses.Data (HorizontalSpace e)) := ⟨ReferenceClasses.anchorOffsets (fun _ => 0)⟩
  let filler : Environment d := fun _ => Classical.choice ‹Nonempty (Row d)›
  let μ : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
    ⟨rawCurrentOccupation e ν Q (fun i ω => t ω i) (fun i => ht i) filler N m,inferInstance⟩
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,inferInstance⟩
  have he := rawCurrentOccupation_actual e ν Q t J ht hJ hst filler N m M hact
  have hmass : (μ : Measure (RawCurrentData e × LocalUpperField e)).real Set.univ=
      (ρ : Measure (ActualEpisodeArray e)).real Set.univ :=
    Entropy.real_mass_eq_of_maps_equal _ _ _ _ (rawCurrentProjection_measurable e)
      (typedCurrentArrayWindow_measurable e 0 m) he
  have hμpos : 0<(μ : Measure (RawCurrentData e × LocalUpperField e)).real Set.univ := by rw [hmass]; exact hpos
  have hn := Entropy.normalize_maps_equal μ ρ (rawCurrentProjection e) (typedCurrentArrayWindow e 0 m)
    (rawCurrentProjection_measurable e) (typedCurrentArrayWindow_measurable e 0 m)
    (finiteMeasure_ne_zero_of_real_mass_pos μ hμpos) (finiteMeasure_ne_zero_of_real_mass_pos ρ hpos) he
  have hb := currentOccupation_kl_le e ν Q hfin (fun i ω => t ω i)
    (fun i => ht i) (fun i => hst i) hmono filler N m hμpos
  change klDiv ((μ.normalize : Measure _).map (rawCurrentProjection e))
    (((μ.normalize : Measure _).map (rawCurrentProjection e)).fst.compProd (currentWindowReference e ν)) ≤ _ at hb
  rw [hn] at hb
  change klDiv ((ρ.normalize : Measure _).map (typedCurrentArrayWindow e 0 m))
    (((ρ.normalize : Measure _).map (typedCurrentArrayWindow e 0 m)).fst.compProd (currentWindowReference e ν)) ≤ _
  convert hb using 1
  exact congrArg (fun x : ℝ => ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal/x)) hmass.symm

end DirectionalTransience

end

end OAI
