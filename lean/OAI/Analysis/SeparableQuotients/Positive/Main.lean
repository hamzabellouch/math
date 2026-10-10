import OAI.Analysis.SeparableQuotients.Positive.RowQuotients
import OAI.Analysis.SeparableQuotients.Positive.TransfiniteFamily
import OAI.Analysis.SeparableQuotients.Positive.UnconditionalBasis
import OAI.Analysis.SeparableQuotients.Positive.FieldTransfer
import OAI.Analysis.SeparableQuotients.Main

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient
namespace Integration



theorem small_type_additive
    (μ : @Measure ℝ ⊤)
    (hadd : ∀ (s : Set ℝ), Cardinal.mk s < Cardinal.mk ℝ →
      ∀ (A : s → Set ℝ), Pairwise (fun i j => Disjoint (A i) (A j)) →
        μ (⋃ i, A i) = ∑' i, μ (A i))
    (ι : Type) (hι : Cardinal.mk ι < Cardinal.continuum)
    (A : ι → Set ℝ) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    μ (⋃ i, A i) = ∑' i, μ (A i) := by
  classical
  have hi : Cardinal.mk ι ≤ Cardinal.mk ℝ := by
    simpa only [Cardinal.mk_real] using hι.le
  obtain ⟨e⟩ := Cardinal.le_def ι ℝ |>.mp hi
  let s : Set ℝ := Set.range e
  let d : ι ≃ s := Equiv.ofInjective e e.injective
  have hs : Cardinal.mk s < Cardinal.mk ℝ := by
    rw [← Cardinal.mk_congr d, Cardinal.mk_real]
    exact hι
  have hd := hadd s hs (fun j => A (d.symm j)) (fun j k h =>
    hA (fun h' => h (d.symm.injective h')))
  rw [d.symm.surjective.iUnion_comp, d.symm.tsum_eq (fun i => μ (A i))] at hd
  exact hd



theorem realValuedMeasurableContinuum_iff_index :
    RealValuedMeasurableContinuum ↔
      ∃ μ : Measure Positive.Rows.ContinuumIndex,
        IsProbabilityMeasure μ ∧ Positive.Rows.ContinuumAdditive μ ∧
          ∀ i, μ {i} = 0 := by
  classical
  let : MeasurableSpace ℝ := ⊤
  let e : ℝ ≃ Positive.Rows.ContinuumIndex :=
    Classical.choice (Cardinal.eq.mp (by simp [Positive.Rows.ContinuumIndex, Cardinal.mk_real]))
  constructor
  · rintro ⟨ν, hν, hsingle, hadd⟩
    let : IsProbabilityMeasure ν := ⟨hν⟩
    let μ : Measure Positive.Rows.ContinuumIndex := ν.map e
    refine ⟨μ, inferInstance, ?_, ?_⟩
    · intro ι hι A hA
      have hd : Pairwise (fun i j => Disjoint (e ⁻¹' A i) (e ⁻¹' A j)) := by
        intro i j hij
        exact (hA hij).preimage e
      simpa only [μ, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
        Set.preimage_iUnion] using small_type_additive ν hadd ι hι _ hd
    · intro i
      rw [show μ = ν.map e from rfl,
        Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
      simpa only [Set.preimage, Set.mem_singleton_iff, ← e.eq_symm_apply, Set.ofPred_eq_eq_singleton]
        using hsingle (e.symm i)
  · rintro ⟨μ, hp, hadd, hsingle⟩
    let : IsProbabilityMeasure μ := hp
    let ν : @Measure ℝ ⊤ := μ.map e.symm
    have : IsProbabilityMeasure ν := inferInstance
    refine ⟨ν, measure_univ, ?_, ?_⟩
    · intro x
      rw [show ν = μ.map e.symm from rfl,
        Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
      simpa only [Set.preimage, Set.mem_singleton_iff, e.symm_apply_eq, Set.ofPred_eq_eq_singleton]
        using hsingle (e x)
    · intro s hs A hA
      have hd : Pairwise (fun i j => Disjoint (e.symm ⁻¹' A i) (e.symm ⁻¹' A j)) := by
        intro i j hij
        exact (hA hij).preimage e.symm
      simpa only [ν, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
        Set.preimage_iUnion] using hadd s (by simpa only [Cardinal.mk_real] using hs) _ hd

end Integration

namespace Integration



theorem measurable_continuum_regular (h : RealValuedMeasurableContinuum) :
    Cardinal.IsRegular Cardinal.continuum.{0} := by
  obtain ⟨μ, hp, hadd, hsingle⟩ := realValuedMeasurableContinuum_iff_index.mp h
  let : IsProbabilityMeasure μ := hp
  exact Positive.Rows.continuum_regular μ hadd hsingle

universe u



theorem SQ_real_iff_complex : SQ.{u} ℝ ↔ SQ.{u} ℂ := by
  constructor
  · intro h X _ _ _ hinf
    let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
    have hr : ¬ FiniteDimensional ℝ X := by
      intro hh
      let := hh
      exact hinf (Module.Finite.of_restrictScalars_finite ℝ ℂ X)
    exact Positive.Fields.ComplexTransfer.positive_transfer (h X hr)
  · intro h X _ _ _ hinf
    by_contra hn
    exact complexify_noSQ X hn (h (Complexify X) (Complexify.infinite X hinf))

end Integration
end SeparableQuotient

end

end

end OAI
