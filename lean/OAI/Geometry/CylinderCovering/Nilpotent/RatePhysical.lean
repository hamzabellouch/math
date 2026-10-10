import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateTheorem

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CylinderCovering.NilpotentRate

lemma tile_isSquareTile (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ}
    (hτ : 0 < τ) (i : Index) : RuledApproximation.IsSquareTile (tile Q τ i) := by
  refine ⟨τ • Q (integerVector i), Q, τ, hτ, ?_⟩
  simp only [tile, map_add, smul_add]

theorem construction_enumeration {δ R h : ℝ} (hδ : 0 < δ)
    {D : Set Plane} {G : Plane → Plane} {tag : Index → Plane}
    {Q : Index → Plane ≃ₗᵢ[ℝ] Plane}
    (hfin : (retainedIndices δ R D Q).Finite) :
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      n = Nat.card (retainedIndices δ R D Q) ∧
      (∀ i, RuledApproximation.IsSquareTile (T i)) ∧
      (⋃ i, RuledApproximation.auxiliaryCylinder (T i) (g i)) =
        constructionCarrier δ R D G tag Q ∧
      (∑ i, volume.real (T i) * RuledApproximation.physicalWeight h (g i)) =
        constructionCost h δ R D G tag Q := by
  classical
  let := hfin.fintype
  let e := (Fintype.equivFin (retainedIndices δ R D Q)).symm
  let T := fun i => tile (Q (e i).val.1) (δ ^ 2) (e i).val.2
  let g := fun i => affineVelocity G tag (e i).val.1
    (fineCenter δ (Q (e i).val.1) (e i).val.2)
  refine ⟨_, T, g, ?_, ?_, ?_, ?_⟩
  · exact Nat.card_eq_fintype_card.symm
  · intro i
    exact tile_isSquareTile _ (sq_pos_of_pos hδ) _
  · ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨(e i).val, mem_iUnion.mpr ⟨(e i).property, hi⟩⟩
    · intro hz
      obtain ⟨ij, hij⟩ := mem_iUnion.mp hz
      obtain ⟨hret, hz⟩ := mem_iUnion.mp hij
      obtain ⟨i, hi⟩ := e.surjective ⟨ij, hret⟩
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simpa only [T, g, hi] using hz
  · unfold constructionCost
    rw [tsum_fintype]
    exact e.sum_comp (fun ij => volume.real (tile (Q ij.val.1) (δ ^ 2) ij.val.2) *
      RuledApproximation.physicalWeight h
        (affineVelocity G tag ij.val.1 (fineCenter δ (Q ij.val.1) ij.val.2)))

theorem construction_physical_realization {δ R h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    {D : Set Plane} {G : Plane → Plane} {tag : Index → Plane}
    {Q : Index → Plane ≃ₗᵢ[ℝ] Plane}
    (hfin : (retainedIndices δ R D Q).Finite) (a : ℝ) :
    ∃ n : ℕ, ∃ C₁ C₂ : Fin n → RuledApproximation.Cylinder,
      n = Nat.card (retainedIndices δ R D Q) ∧
      (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram) ∧
      RuledApproximation.familySet C₁ = RuledApproximation.firstPhysicalMap h ''
        constructionCarrier δ R D G tag Q ∧
      RuledApproximation.familySet C₂ = RuledApproximation.secondPhysicalMap h a ''
        constructionCarrier δ R D G tag Q ∧
      RuledApproximation.familyArea C₁ = h * constructionCost h δ R D G tag Q ∧
      RuledApproximation.familyArea C₂ = h * constructionCost h δ R D G tag Q := by
  classical
  obtain ⟨n, T, g, hn, hT, hcarrier, hcost⟩ :=
    construction_enumeration (h := h) (G := G) (tag := tag) hδ hfin
  let C₁ : Fin n → RuledApproximation.Cylinder := fun i =>
    RuledApproximation.projectedCylinder h (g i) (T i)
  let C₂ : Fin n → RuledApproximation.Cylinder := fun i =>
    ((C₁ i).rotate RuledApproximation.swapReflect).translate
      (RuledApproximation.vec3 0 0 (h*a))
  have hfirst (i : Fin n) : (C₁ i).carrier = RuledApproximation.firstPhysicalMap h ''
      RuledApproximation.auxiliaryCylinder (T i) (g i) :=
    RuledApproximation.projectedCylinder_carrier h _ _
  have hsecond (i : Fin n) : (C₂ i).carrier = RuledApproximation.secondPhysicalMap h a ''
      RuledApproximation.auxiliaryCylinder (T i) (g i) := by
    dsimp only [C₂]
    rw [RuledApproximation.Cylinder.translate_carrier,
      RuledApproximation.Cylinder.rotate_carrier, hfirst, ← image_comp, ← image_comp]
    congr 1
    funext z
    exact (RuledApproximation.physicalMaps_relation h a z).symm
  have harea : RuledApproximation.familyArea C₁ =
      h * constructionCost h δ R D G tag Q := by
    rw [← hcost, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (C₁ i).area = h * volume.real (T i) *
      RuledApproximation.physicalWeight h (g i) from
      RuledApproximation.projectedCylinder_area hh _ _]
    ring
  refine ⟨n, C₁, C₂, hn, ?_, ?_, ?_, harea, ?_⟩
  · intro i
    have hi : (C₁ i).parallelogram :=
      RuledApproximation.projectedCylinder_parallelogram hh _ (hT i).parallelogram
    exact ⟨hi, RuledApproximation.Cylinder.translate_parallelogram
      (RuledApproximation.Cylinder.rotate_parallelogram hi _) _⟩
  · simp only [RuledApproximation.familySet, hfirst, ← image_iUnion, hcarrier]
  · simp only [RuledApproximation.familySet, hsecond, ← image_iUnion, hcarrier]
  · calc
      RuledApproximation.familyArea C₂ = RuledApproximation.familyArea C₁ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (RuledApproximation.Cylinder.translate_area _ _).trans
          (RuledApproximation.Cylinder.rotate_area _ _)
      _ = _ := harea

theorem smoothRate_physical (D : Set Plane) (G : Plane → Plane) (h : ℝ)
    (hD : IsCompact D) (hG : BoundedSecondNear D G)
    (hnil : ∀ p ∈ D, (fderiv ℝ G p).comp (fderiv ℝ G p) = 0) (hh : 0 < h) :
    ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ a : ℝ,
      ∃ n : ℕ, ∃ C₁ C₂ : Fin n → RuledApproximation.Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram) ∧
        RuledApproximation.physicalRuled h D G 1 ⊆ RuledApproximation.familySet C₁ ∧
        RuledApproximation.secondPhysicalMap h a '' RuledApproximation.physicalRuled 1 D G 1 ⊆
          RuledApproximation.familySet C₂ ∧
        RuledApproximation.familyArea C₁ ≤
          h * (∫ b in gridUnion δ D, RuledApproximation.physicalWeight h (G b)) + C * δ ∧
        RuledApproximation.familyArea C₁ ≤
          h * (∫ b in D, RuledApproximation.physicalWeight h (G b)) +
            h * volume.real (gridUnion δ D \ D) + C * δ ∧
        RuledApproximation.familyArea C₂ = RuledApproximation.familyArea C₁ := by
  obtain ⟨_, M, K, C, δ₀, _, _, hC, hδ₀, hdata⟩ := smoothRate D G h hD hG hnil hh
  refine ⟨h*C, δ₀, mul_nonneg hh.le hC, hδ₀, ?_⟩
  intro δ hδ hsmall a
  obtain ⟨tag, Q, _, hfin, hcover, hunion, hdomain⟩ := hdata δ hδ hsmall
  obtain ⟨n, C₁, C₂, _, hshape, hfirst, hsecond, harea₁, harea₂⟩ :=
    construction_physical_realization (G := G) (tag := tag) (Q := Q) hδ hh hfin a
  refine ⟨n, C₁, C₂, hshape, ?_, ?_, ?_, ?_, harea₂.trans harea₁.symm⟩
  · rw [hfirst, ← RuledApproximation.firstPhysicalMap_ruled]
    exact image_mono hcover
  · rw [hsecond]
    exact image_mono hcover
  · rw [harea₁]
    calc
      _ ≤ h * ((∫ b in gridUnion δ D, RuledApproximation.physicalWeight h (G b)) + C*δ) :=
        mul_le_mul_of_nonneg_left hunion hh.le
      _ = _ := by ring
  · rw [harea₁]
    calc
      _ ≤ h * ((∫ b in D, RuledApproximation.physicalWeight h (G b)) +
          volume.real (gridUnion δ D \ D) + C*δ) := mul_le_mul_of_nonneg_left hdomain hh.le
      _ = _ := by ring

end CylinderCovering.NilpotentRate

end

end OAI
