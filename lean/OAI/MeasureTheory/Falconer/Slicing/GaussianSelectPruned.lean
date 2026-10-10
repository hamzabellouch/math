import OAI.MeasureTheory.Falconer.Slicing.GaussianParameterSupport
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedIncidence
import OAI.MeasureTheory.Falconer.Slicing.SliceSelectionMean

namespace OAI

/-! # Quantitative selection of a retained slice in the controlled row chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_zero_of_point_mass
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1)))
    (p : (Fin h → Space (n+1)) × Space h) (hp : gaussianPointMass μ δ p = 0) :
    gaussianPrunedIncidence μ ν δ r TP TD M E p = 0 := by
  have hz : gaussianPointSliceMeasure μ p.1 p.2 δ = 0 :=
    Measure.measure_univ_eq_zero.mp (by rw [gaussianPointSliceMeasure_univ]; exact hp)
  simp only [gaussianPrunedIncidence,hz,Measure.restrict_zero,Measure.zero_prod,Measure.coe_zero,Pi.zero_apply]

theorem gaussian_pruned_parameter_support
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) :
    ∀ᵐ p ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p ∉ (gaussianRowNeighborhood B ε) ×ˢ (coordinateBox h (D*(ε+1)+δ)) →
      gaussianPrunedIncidence μ ν δ r TP TD M E p = 0 := by
  have ha : ∀ᵐ p : (Fin h → Space (n+1)) × Space h
      ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p.1 ∈ gaussianRowNeighborhood B ε :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (gaussianRowNeighborhood_measurable B ε))
  filter_upwards [ha] with p hp hnot
  have hz : p.2 ∉ coordinateBox h (D*(ε+1)+δ) := fun hz => hnot ⟨hp,hz⟩
  apply gaussian_pruned_incidence_zero_of_point_mass μ ν δ r TP TD M E p
  exact gaussian_point_mass_zero_outside_box μ p.1 (by linarith)
    (gaussianRowNeighborhood_norm B hB hp) hμ hz

theorem gaussian_select_pruned_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) {a : ℝ≥0∞}
    (hmean : a*volume (coordinateBox h (D*(ε+1)+δ)) <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      a < gaussianPrunedIncidence μ ν δ r TP TD M E (A,z) := by
  let G := gaussianRowNeighborhood B ε
  let Z := coordinateBox h (D*(ε+1)+δ)
  let ξ := ((gaussianRows (n+1) h).restrict G).prod (volume : Measure (Space h))
  have hmass : ξ (G ×ˢ Z) ≤ volume Z := by
    rw [Measure.prod_prod]
    have hg : ((gaussianRows (n+1) h).restrict G) G ≤ 1 := by
      calc
        _ ≤ gaussianRows (n+1) h G := Measure.restrict_le_self _
        _ ≤ gaussianRows (n+1) h univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    simpa only [one_mul] using mul_le_mul_left hg (volume Z)
  have hgt : a*ξ (G ×ˢ Z) < ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ :=
    (mul_le_mul_right hmass a).trans_lt hmean
  obtain ⟨⟨A,z⟩,hAz,hi⟩ := exists_large_slice_of_mean ξ (G ×ˢ Z)
    ((gaussianRowNeighborhood_measurable B ε).prod (coordinateBox_measurable _)) _
    (gaussian_pruned_parameter_support B hB hε μ ν hμ δ r TP TD M E) hgt
  exact ⟨A,hAz.1,z,hAz.2,hi⟩

end Falconer

end OAI
