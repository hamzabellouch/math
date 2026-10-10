import OAI.Analysis.CoulombTransport.BorelTransport
import OAI.Analysis.CoulombTransport.ContinuousCDF
import OAI.Analysis.CoulombTransport.AtomlessMap

namespace OAI

universe uX uY

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal unitInterval

namespace Problem356.Transport

/-- Every atomless standard Borel probability admits a uniform random variable. -/
theorem exists_uniform_map {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ f : X → I, Measurable f ∧ Measure.map f μ = volume := by
  let e := embeddingReal X
  have he : Measurable e := measurable_embeddingReal X
  let η := Measure.map e μ
  have : IsProbabilityMeasure η := inferInstance
  have : NullSingletonClass η := nullSingletonClass_map_embeddingReal μ
  have hc : Continuous (cdf η) := continuous_cdf_of_nullSingletonClass η
  let F : ℝ → I := fun x => ⟨cdf η x, cdf_nonneg η x, cdf_le_one η x⟩
  have hF : Measurable F := hc.measurable.subtype_mk
  refine ⟨F ∘ e, hF.comp he, ?_⟩
  rw [← Measure.map_map hF he]
  exact map_cdf_unitInterval η hc

/-- A singleton-null standard Borel probability can be transported measurably to
any probability on a nonempty standard Borel target. -/
theorem exists_measurable_transport {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ] :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  obtain ⟨f, hf, hfμ⟩ := exists_uniform_map μ
  obtain ⟨g, hg, hgν⟩ := ν.exists_measurable_map_eq
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  rw [← Measure.map_map hg hf, hfμ, hgν]

/-- Equal finite masses can be transported provided the source has no point atoms. -/
theorem exists_measurable_transport_finite {X : Type uX} {Y : Type uY}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ]
    (hmass : μ univ = ν univ) :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [← hmass, hμ]
      simp
    exact ⟨fun _ => Classical.choice inferInstance, measurable_const, by simp [hμ, hν]⟩
  · have : NeZero μ := ⟨hμ⟩
    have hν : ν ≠ 0 := by
      intro hν
      apply hμ
      apply Measure.measure_univ_eq_zero.mp
      rw [hmass, hν]
      simp
    have : NeZero ν := ⟨hν⟩
    have : NullSingletonClass ((μ univ)⁻¹ • μ) := ⟨fun x => by simp⟩
    obtain ⟨Q, hQ, hmap⟩ := exists_measurable_transport
      ((μ univ)⁻¹ • μ) ((ν univ)⁻¹ • ν)
    refine ⟨Q, hQ, ?_⟩
    have hscale := congrArg (fun m : Measure Y => μ univ • m) hmap
    rw [Measure.map_smul _ hQ.aemeasurable, smul_smul, ENNReal.mul_inv_cancel
      (NeZero.ne (μ univ)) (measure_ne_top μ univ), one_smul] at hscale
    rw [hmass, smul_smul, ENNReal.mul_inv_cancel
      (NeZero.ne (ν univ)) (measure_ne_top ν univ), one_smul] at hscale
    exact hscale

/-- A restricted atomless measure can be redistributed proportionally over any
positive-mass target cell. The input cell is allowed to have mass zero. -/
theorem exists_measurable_transport_restrict {X : Type uX}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (A B : Set X) (hA : μ A ≠ 0) :
    ∃ Q : X → X, Measurable Q ∧
      Measure.map Q (μ.restrict B) = (μ B / μ A) • μ.restrict A := by
  have hmass : ((μ B / μ A) • μ.restrict A) univ = μ B := by
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.div_mul_cancel hA (measure_ne_top μ A)
  have : IsFiniteMeasure ((μ B / μ A) • μ.restrict A) :=
    ⟨by rw [hmass]; exact measure_lt_top μ B⟩
  apply exists_measurable_transport_finite
  rw [Measure.restrict_apply_univ, hmass]

/-- The transport to a measurable target cell can be chosen to take every value
inside that cell, by resetting outputs on a source-null set. -/
theorem exists_measurable_transport_restrict_mem {X : Type uX}
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (A B : Set X) (hAm : MeasurableSet A) (hA : μ A ≠ 0) :
    ∃ Q : X → X, Measurable Q ∧
      Measure.map Q (μ.restrict B) = (μ B / μ A) • μ.restrict A ∧
      ∀ x, Q x ∈ A := by
  classical
  obtain ⟨Q, hQ, hmap⟩ := exists_measurable_transport_restrict μ A B hA
  obtain ⟨a, ha⟩ := nonempty_of_measure_ne_zero hA
  let R : X → X := fun x => if Q x ∈ A then Q x else a
  have hR : Measurable R := hQ.ite (hAm.preimage hQ) measurable_const
  have hmem : ∀ᵐ x ∂μ.restrict B, Q x ∈ A := by
    apply (ae_map_iff hQ.aemeasurable hAm).mp
    rw [hmap]
    exact Measure.ae_smul_measure (ae_restrict_mem hAm) _
  have heq : R =ᵐ[μ.restrict B] Q := by
    filter_upwards [hmem] with x hx
    simp [R, hx]
  refine ⟨R, hR, (Measure.map_congr heq).trans hmap, ?_⟩
  intro x
  by_cases hx : Q x ∈ A <;> simp [R, hx, ha]

end Problem356.Transport

end

end OAI
