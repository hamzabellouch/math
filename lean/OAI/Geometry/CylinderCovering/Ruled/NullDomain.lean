import OAI.Geometry.CylinderCovering.Nilpotent.C1

namespace OAI

noncomputable section
open Set MeasureTheory

namespace RuledApproximation

theorem empty_physical_pair (G : Plane → Plane) (h a L : ℝ) :
    ∃ C₁ C₂ : Fin 0 → Cylinder,
      (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram) ∧
      physicalRuled h ∅ G L ⊆ familySet C₁ ∧
      secondPhysicalMap h a '' physicalRuled 1 ∅ G L ⊆ familySet C₂ ∧
      familyArea C₁ = 0 ∧ familyArea C₂ = 0 := by
  refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, ?_, ?_, ?_⟩
  · simp [physicalRuled_empty]
  · simp [physicalRuled_empty]
  · simp [familyArea]
  · simp [familyArea]

theorem null_domain_physical_pair {D : Set Plane} {G : Plane → Plane}
    (hD : IsCompact D) (hnull : volume D = 0) (hG : SmoothNear 1 D G)
    (hnil : ∀ b ∈ D, (fderiv ℝ G b).comp (fderiv ℝ G b) = 0)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (a : ℝ) :
    ∃ n : ℕ, ∃ C₁ C₂ : Fin n → Cylinder,
      (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
        IsCompact (C₁ i).base ∧ IsCompact (C₂ i).base ∧
        Convex ℝ (C₁ i).base ∧ Convex ℝ (C₂ i).base) ∧
      physicalRuled h D G 1 ⊆ familySet C₁ ∧
      secondPhysicalMap h a '' physicalRuled 1 D G 1 ⊆ familySet C₂ ∧
      familyArea C₁ = familyArea C₂ ∧ familyArea C₁ + familyArea C₂ < ε := by
  obtain ⟨n, T, g, _hT, hcover, hcost, hphysical⟩ :=
    nilpotentC1 D G hD hG hnil h (ε / (4 * h)) hh (by positivity)
  rw [setIntegral_measure_zero _ hnull, zero_add] at hcost
  obtain ⟨C₁, C₂, hC⟩ := hphysical a
  have harea₁ : familyArea C₁ = h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
    unfold familyArea
    simp_rw [(hC _).2.2.2.2.1, mul_assoc]
    rw [Finset.mul_sum]
  have harea₂ : familyArea C₂ = h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
    unfold familyArea
    simp_rw [(hC _).2.2.2.2.2, mul_assoc]
    rw [Finset.mul_sum]
  refine ⟨n, C₁, C₂, ?_, ?_, ?_, harea₁.trans harea₂.symm, ?_⟩
  · intro i
    obtain ⟨hpar₁, hpar₂, _⟩ := hC i
    exact ⟨hpar₁, hpar₂, hpar₁.isCompact, hpar₂.isCompact,
      hpar₁.convex, hpar₂.convex⟩
  · rw [← firstPhysicalMap_ruled]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
    exact mem_iUnion.mpr ⟨i, (hC i).2.2.1 ▸ mem_image_of_mem _ hi⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
    exact mem_iUnion.mpr ⟨i, (hC i).2.2.2.1 ▸ mem_image_of_mem _ hi⟩
  · rw [harea₁, harea₂]
    have hc := mul_le_mul_of_nonneg_left hcost hh.le
    have he : h * (ε / (4 * h)) = ε / 4 := by field_simp
    rw [he] at hc
    linarith

theorem null_domain_physical_pair_of_fderiv_zero
    {D : Set Plane} {G : Plane → Plane}
    (hD : IsCompact D) (hnull : volume D = 0) (hG : SmoothNear 1 D G)
    (hzero : ∀ b ∈ D, fderiv ℝ G b = 0)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (a : ℝ) :
    ∃ n : ℕ, ∃ C₁ C₂ : Fin n → Cylinder,
      (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
        IsCompact (C₁ i).base ∧ IsCompact (C₂ i).base ∧
        Convex ℝ (C₁ i).base ∧ Convex ℝ (C₂ i).base) ∧
      physicalRuled h D G 1 ⊆ familySet C₁ ∧
      secondPhysicalMap h a '' physicalRuled 1 D G 1 ⊆ familySet C₂ ∧
      familyArea C₁ = familyArea C₂ ∧ familyArea C₁ + familyArea C₂ < ε := by
  apply null_domain_physical_pair hD hnull hG _ hh hε a
  intro b hb
  simp [hzero b hb]

end RuledApproximation

end

end OAI
