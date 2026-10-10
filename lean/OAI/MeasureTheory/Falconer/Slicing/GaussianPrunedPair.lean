import OAI.MeasureTheory.Falconer.Slicing.GaussianSelectPruned

namespace OAI

/-! # Measurable parameter-dependent incidence on the retained original laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

noncomputable def gaussianPrunedPairMass
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)))
    (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  gaussianPrunedIncidence μ ν δ r TP TD M {t | (p,t) ∈ G} p

theorem gaussianPrunedPairMass_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d))) (hG : MeasurableSet G) :
    Measurable (gaussianPrunedPairMass μ ν δ r TP TD M G) := by
  let F : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {q | q ∈ G ∧ q.2.1 ∈ gaussianPointGood μ δ r TP q.1 ∧
      q.2.2 ∈ gaussianDirectionGood ν δ r TD M q.1.1}
  have hF : MeasurableSet F := by
    have hp := (gaussianPointGood_measurable_joint (h := h) μ δ r TP).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1,q.2.1)) from by fun_prop)
    have hd := (gaussianDirectionGood_measurable_joint (h := h) ν δ r TD M).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1.1,q.2.2)) from by fun_prop)
    exact hG.inter (hp.inter hd)
  convert gaussian_pair_restriction_mass_measurable μ ν δ F hF using 1
  ext p
  rw [gaussianPrunedPairMass,gaussianPrunedIncidence,Measure.prod_restrict,
    Measure.restrict_apply (show MeasurableSet {t | (p,t) ∈ G} from
      hG.preimage measurable_prodMk_left)]
  congr 1

omit [Fintype ι] in
theorem gaussianPrunedPairMass_parameter_support {n : ℕ}
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1)))) :
    ∀ᵐ p ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p ∉ (gaussianRowNeighborhood B ε) ×ˢ (coordinateBox h (D*(ε+1)+δ)) →
      gaussianPrunedPairMass μ ν δ r TP TD M G p = 0 := by
  have ha : ∀ᵐ p : (Fin h → Space (n+1)) × Space h
      ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p.1 ∈ gaussianRowNeighborhood B ε :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (gaussianRowNeighborhood_measurable B ε))
  filter_upwards [ha] with p hp hnot
  apply gaussian_pruned_incidence_zero_of_point_mass μ ν δ r TP TD M _ p
  apply gaussian_point_mass_zero_outside_box μ p.1 (by linarith)
    (gaussianRowNeighborhood_norm B hB hp) hμ
  exact fun hz => hnot ⟨hp,hz⟩

omit [Fintype ι] in
theorem gaussian_select_pruned_pair {n : ℕ}
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1))))
    {a : ℝ≥0∞}
    (hmean : a*volume (coordinateBox h (D*(ε+1)+δ)) <
      ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M G p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      a < gaussianPrunedPairMass μ ν δ r TP TD M G (A,z) := by
  let U := gaussianRowNeighborhood B ε
  let Z := coordinateBox h (D*(ε+1)+δ)
  let ξ := ((gaussianRows (n+1) h).restrict U).prod (volume : Measure (Space h))
  have hmass : ξ (U ×ˢ Z) ≤ volume Z := by
    rw [Measure.prod_prod]
    have hg : ((gaussianRows (n+1) h).restrict U) U ≤ 1 := by
      calc
        _ ≤ gaussianRows (n+1) h U := Measure.restrict_le_self _
        _ ≤ gaussianRows (n+1) h univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    simpa only [one_mul] using mul_le_mul_left hg (volume Z)
  have hgt : a*ξ (U ×ˢ Z) < ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M G p ∂ξ :=
    (mul_le_mul_right hmass a).trans_lt hmean
  obtain ⟨⟨A,z⟩,hAz,hi⟩ := exists_large_slice_of_mean ξ (U ×ˢ Z)
    ((gaussianRowNeighborhood_measurable B ε).prod (coordinateBox_measurable _)) _
    (gaussianPrunedPairMass_parameter_support B hB hε μ ν hμ δ r TP TD M G) hgt
  exact ⟨A,hAz.1,z,hAz.2,hi⟩

end Falconer

end OAI
