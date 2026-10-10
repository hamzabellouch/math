import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336AdditiveD139.CylindricalIndependence

variable {Ω : Type u_1} {I : Type u_2} {E : I → Type u_3} [∀ i, MeasurableSpace (E i)]

theorem law_and_indep_of_finite_restrictions
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure (∀ i, E i)) [IsProbabilityMeasure ν]
    (D : Ω → ∀ i, E i) (hD : Measurable D)
    (hfinite : ∀ S : Finset I,
      Measure.map (fun ω => S.restrict (D ω)) μ = Measure.map S.restrict ν ∧
        Indep m (MeasurableSpace.comap (fun ω => S.restrict (D ω)) inferInstance) μ) :
    Measure.map D μ = ν ∧ Indep m (MeasurableSpace.comap D inferInstance) μ := by
  have hrestrictFinite (A : Set Ω) (hA : MeasurableSet[m] A) (S : Finset I) :
      Measure.map (fun ω => S.restrict (D ω)) (μ.restrict A) =
        μ A • Measure.map S.restrict ν := by
    have hDS : Measurable (fun ω => S.restrict (D ω)) :=
      (Finset.measurable_restrict S).comp hD
    ext B hB
    rw [Measure.map_apply hDS hB, Measure.restrict_apply (hDS hB),
      Measure.smul_apply, Measure.map_apply (Finset.measurable_restrict S) hB]
    have hmass := congrArg (fun ρ : Measure (∀ i : S, E i) => ρ B) (hfinite S).1
    rw [Measure.map_apply hDS hB,
      Measure.map_apply (Finset.measurable_restrict S) hB] at hmass
    have hind := (Indep_iff _ _ _).1 (hfinite S).2 A
      ((fun ω => S.restrict (D ω)) ⁻¹' B) hA ⟨B, hB, rfl⟩
    simpa only [Set.inter_comm, hmass, smul_eq_mul] using hind
  have hrestrict (A : Set Ω) (hA : MeasurableSet[m] A) :
      Measure.map D (μ.restrict A) = μ A • ν := by
    let : IsFiniteMeasure (μ A • ν) := ν.smul_finite (measure_ne_top μ A)
    let P : (S : Finset I) → Measure (∀ i : S, E i) :=
      fun S => Measure.map S.restrict (μ A • ν)
    have hleft : IsProjectiveLimit (Measure.map D (μ.restrict A)) P := by
      intro S
      rw [Measure.map_map (Finset.measurable_restrict S) hD]
      change Measure.map (fun ω => S.restrict (D ω)) (μ.restrict A) = _
      rw [hrestrictFinite A hA S]
      exact (Measure.map_smul _ (Finset.measurable_restrict S).aemeasurable).symm
    have hright : IsProjectiveLimit (μ A • ν) P := fun _ => rfl
    exact hleft.unique hright
  have hlaw : Measure.map D μ = ν := by
    simpa using hrestrict Set.univ MeasurableSet.univ
  refine ⟨hlaw, (Indep_iff _ _ _).2 ?_⟩
  intro A B hA hB
  obtain ⟨C, hC, rfl⟩ := hB
  have h := congrArg (fun ρ : Measure (∀ i, E i) => ρ C) (hrestrict A hA)
  rw [Measure.map_apply hD hC, Measure.restrict_apply (hD hC),
    Measure.smul_apply] at h
  rw [Set.inter_comm] at h
  rw [← Measure.map_apply hD hC, hlaw]
  exact h

theorem product_law_and_indep_of_finite_restrictions
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (ν i)]
    (D : Ω → ∀ i, E i) (hD : Measurable D)
    (hfinite : ∀ S : Finset I,
      Measure.map (fun ω => S.restrict (D ω)) μ = Measure.pi (fun i : S => ν i) ∧
        Indep m (MeasurableSpace.comap (fun ω => S.restrict (D ω)) inferInstance) μ) :
    Measure.map D μ = Measure.infinitePi ν ∧
      Indep m (MeasurableSpace.comap D inferInstance) μ := by
  apply law_and_indep_of_finite_restrictions m μ (Measure.infinitePi ν) D hD
  intro S
  simpa only [Measure.infinitePi_map_restrict] using hfinite S

end Problem336AdditiveD139.CylindricalIndependence

end

end OAI
