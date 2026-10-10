import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.VolumeExistence

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume

lemma measure_eq_of_restrict_cover {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hcover : ⋃ n, U n = univ) (heq : ∀ n, μ.restrict (U n) = ν.restrict (U n)) : μ = ν := by
  let D := disjointed U
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hU
  have hDc : ⋃ n, D n = univ := iUnion_disjointed.trans hcover
  have hrestr : ∀ n, μ.restrict (D n) = ν.restrict (D n) := by
    intro n
    rw [← Measure.restrict_restrict_of_subset (disjointed_subset U n),heq n,
      Measure.restrict_restrict_of_subset (disjointed_subset U n)]
  calc
    μ = μ.restrict (⋃ n, D n) := by rw [hDc,Measure.restrict_univ]
    _ = Measure.sum (fun n => μ.restrict (D n)) :=
      Measure.restrict_iUnion (disjoint_disjointed U) hD
    _ = Measure.sum (fun n => ν.restrict (D n)) := by simp_rw [hrestr]
    _ = ν.restrict (⋃ n, D n) := (Measure.restrict_iUnion (disjoint_disjointed U) hD).symm
    _ = ν := by rw [hDc,Measure.restrict_univ]

attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

lemma measure_eq_of_chart_restrict [IsManifold I 1 M] {μ ν : Measure M}
    (heq : ∀ x : M, μ.restrict (extChartAt I x).source = ν.restrict (extChartAt I x).source) :
    μ = ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact measure_eq_of_restrict_cover μ ν (fun n => (extChartAt I (f n)).source)
      (fun n => (isOpen_extChartAt_source (f n)).measurableSet)
      (eq_univ_of_univ_subset hf) (fun n => heq (f n))

variable [IsManifold I 1 M]

lemma volume_unique (g : Metric (M := M)) {μ ν : Measure M}
    (hμ : IsVolume g μ) (hν : IsVolume g ν) : μ = ν :=
  measure_eq_of_chart_restrict (fun x => (hμ x).trans (hν x).symm)

lemma riemannianVolume_isVolume (g : Metric (M := M)) : IsVolume g (riemannianVolume g) :=
  Classical.epsilon_spec (exists_volume g)
instance riemannianVolume_locallyFinite (g : Metric (M := M)) :
    IsLocallyFiniteMeasure (riemannianVolume g) := volume_locallyFinite g (riemannianVolume_isVolume g)

end CKSIntrinsicVolume

end

end OAI
