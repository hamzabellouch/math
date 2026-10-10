import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryMarking
import OAI.Probability.Ballisticity.Entropy.DominatedEntropy

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

abbrev MarkedCurrentData {d : ℕ} (e : Direction d) := CurrentData e × ℕ
noncomputable def markedData {d : ℕ} (e : Direction d) (p : MarkedArray e) : MarkedCurrentData e :=
  (arrayCurrentData e 0 p.1,p.2)
lemma markedData_measurable {d : ℕ} (e : Direction d) : Measurable (markedData e) :=
  ((arrayCurrentData_measurable e 0).comp measurable_fst).prodMk measurable_snd

noncomputable def selectUpperField {d : ℕ} (e : Direction d)
    (p : ℕ × ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) : UpperRows e :=
  fun z => p.2 (p.1,z)
lemma selectUpperField_measurable {d : ℕ} (e : Direction d) : Measurable (selectUpperField e) := by
  apply Measurable.of_eval
  intro z
  have hm : Measurable (fun p : ReferenceClasses.AllFields (HorizontalSpace e) (Row d) × ℕ => p.1 (p.2,z)) :=
    measurable_from_prod_countable_left (fun a => measurable_pi_apply (a,z))
  exact hm.comp measurable_swap

noncomputable def markedUpper {d : ℕ} (e : Direction d) (n : ℕ) (p : MarkedArray e) : UpperRows e :=
  arrayUpperRows e 0 n p.2 p.1
lemma markedUpper_measurable {d : ℕ} (e : Direction d) (n : ℕ) : Measurable (markedUpper e n) :=
  measurable_from_prod_countable_left (fun a => (arrayUpperRows_continuous e 0 n a).measurable)

lemma marked_window_law {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (n : ℕ) :
    (markedArrayLaw e μ E).map (fun p => (markedData e p,markedUpper e n p)) =
      StoppedWindow.selectedKernel (currentClassKernel e) (selectUpperField e) (selectUpperField_measurable e) ∘ₘ
        (μ[|E].map (typedCurrentArrayWindow e 0 n)) := by
  have hf := (typedCurrentArrayWindow_measurable e 0 n).snd
  have hp : Measurable (fun p : (CurrentData e × ℕ) × ReferenceClasses.AllFields (HorizontalSpace e) (Row d) =>
      (p.1,selectUpperField e (p.1.2,p.2))) :=
    measurable_fst.prodMk ((selectUpperField_measurable e).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h := congrArg (fun M => M.map (fun p : (CurrentData e × ℕ) × ReferenceClasses.AllFields (HorizontalSpace e) (Row d) =>
      (p.1,selectUpperField e (p.1.2,p.2))))
    (StoppedWindow.sample_data_map μ[|E] (arrayCurrentData e 0) (arrayCurrentData_measurable e 0)
      (fun Y => (typedCurrentArrayWindow e 0 n Y).2) hf (currentClassKernel e))
  have hw : Measurable (fun p : ActualEpisodeArray e × ℕ =>
      ((arrayCurrentData e 0 p.1,p.2),(typedCurrentArrayWindow e 0 n p.1).2)) :=
    (((arrayCurrentData_measurable e 0).comp measurable_fst).prodMk measurable_snd).prodMk
      (hf.comp measurable_fst)
  rw [Measure.map_map hp hw,Measure.map_comp _ _ hp] at h
  exact h

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_upper_entropy (L : StationaryArrayLaw ν e)
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) (n : ℕ) :
    let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
    let W := μ.map (fun p => (markedData e p,markedUpper e n p))
    klDiv W (W.fst.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)))≠∞ := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let μ := (L.law : Measure (ActualEpisodeArray e))
  have : IsProbabilityMeasure μ[|G.event] := cond_isProbabilityMeasure G.positive_event.ne'
  let W := μ.map (typedCurrentArrayWindow e 0 n)
  let Q := μ[|G.event].map (typedCurrentArrayWindow e 0 n)
  have : IsProbabilityMeasure W := inferInstance
  have : IsProbabilityMeasure Q := inferInstance
  have hdom : Q≤ENNReal.ofReal ((μ G.event)⁻¹).toReal • W := by
    rw [ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr G.positive_event.ne')]
    have h : μ[|G.event]≤(μ G.event)⁻¹ • μ := smul_le_smul_left _ Measure.restrict_le_self
    simpa only [Measure.map_smul _ (typedCurrentArrayWindow_measurable e 0 n).aemeasurable] using
      Measure.map_mono h (typedCurrentArrayWindow_measurable e 0 n)
  have hk := Entropy.finite_kl_of_domination Q W (W.fst.compProd (currentWindowReference e ν))
    (L.entropy_finite 0 n) _ ENNReal.toReal_nonneg hdom
  have h := StoppedWindow.selected_kl_finite Q W.fst (currentWindowReference e ν) (currentClassKernel e)
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) (selectUpperField e)
    (selectUpperField_measurable e) (fun A a => ReferenceClasses.reference_single_field ν A.1 a) hk
  rw [←marked_window_law e μ G.event n] at h
  exact h

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
