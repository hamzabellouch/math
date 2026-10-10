import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases
import OAI.Geometry.Immersion.ClosedSurface.AtlasLabels

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]

abbrev AtlasCellPhase := ι × (Index × Fin 3)

def atlasSecondTensor (F : M → Space) (p a : M) : Fin 3 → RVec 4 :=
  realSecondTensor (coordinateMap F p) (coordinateChart p a)

def atlasGram (F : M → Space) (p a : M) : ℝ :=
  NormalFrame.gramDet (coordDeriv dx (coordinateMap F p) (coordinateChart p a))
    (coordDeriv dy (coordinateMap F p) (coordinateChart p a))

def atlasActive (p : ι → M) (ψ : ι → M → ℝ) (s : ι → Finset Index)
    (h : ℝ) (a : AtlasCellPhase (ι := ι)) (q : M) : Prop :=
  a.2.1 ∈ s a.1 ∧ q ∈ tsupport (refinedCutoff (p a.1) (ψ a.1) (s a.1) h a.2.1)





omit [T2Space M] [CompactSpace M] in
theorem atlas_phase_weight_constants_with_catalog (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    {ε C : ℝ} (hε : 0 < ε) (σ : Type*) :
    ∃ stock : Finset ℝ, ∃ W κ : ℝ, 0 < W ∧ 0 < κ ∧
      ∀ h : ℝ, 0 < h → ∀ s : ι → Finset Index,
      ∀ ξ : AtlasCellPhase (ι := ι) → SmallModes.Base,
      (∀ a, ‖ξ a‖ ≤ C) →
      ∀ (G : σ → M → Space),
      (∀ t, ContMDiff planeModel spaceModel ∞ (G t)) →
      (∀ t a q, atlasActive p ψ s h a q →
        atlasGram (G t) (p a.1) q ≠ 0 ∧ atlasSecondTensor (G t) (p a.1) q ≠ 0 ∧
        ε*‖atlasSecondTensor (G t) (p a.1) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor (G t) (p a.1) q) (-(ξ a).2,(ξ a).1)‖) →
      ∃ w : AtlasCellPhase (ι := ι) → ℝ, (∀ a, w a ∈ stock) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        ∀ (t : σ) (a b : AtlasCellPhase (ι := ι)) (j : ι) (q : M),
          a ≠ b → atlasActive p ψ s h a q → atlasActive p ψ s h b q → q ∈ tsupport (ψ j) →
          κ*‖atlasSecondTensor (G t) (p j) q‖ ≤
            ‖secondQuadratic (atlasSecondTensor (G t) (p j) q)
              (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
               (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
          κ*‖atlasSecondTensor (G t) (p j) q‖ ≤
            ‖secondQuadratic (atlasSecondTensor (G t) (p j) q)
              (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
               (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
          Good (atlasSecondTensor (G t) (p j) q)
            (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
             w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) ∧
          Good (atlasSecondTensor (G t) (p j) q)
            (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
             w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) := by
  obtain ⟨d,L,hd,hL,hbound⟩ := finite_atlas_transition_bounds p ψ hsource hcompact
  let e := d^2*ε/(4*L^2)
  have he : 0 < e := div_pos (mul_pos (sq_pos_of_pos hd) hε)
    (mul_pos (by norm_num) (sq_pos_of_pos hL))
  obtain ⟨stock,W,κ,hW,hκ,hweights⟩ := quantitative_labeled_phase_lengths_with_catalog
    (ι := AtlasCellPhase (ι := ι)) (X := σ × (ι × M)) (n := 4)
    (C := 2*L*C) (atlasPhaseLabel (ι := ι)) he
  refine ⟨stock,W,κ,hW,hκ,?_⟩
  intro h hh s ξ hξ G hG hlocal
  let B : σ × (ι × M) → Fin 3 → RVec 4 := fun x =>
    atlasSecondTensor (G x.1) (p x.2.1) x.2.2
  let Ξ : AtlasCellPhase (ι := ι) → σ × (ι × M) → SmallModes.Base := fun a x =>
    atlasPhaseCovector (p a.1) (p x.2.1) (ξ a) x.2.2
  let active : AtlasCellPhase (ι := ι) → σ × (ι × M) → Prop := fun a x =>
    atlasActive p ψ s h a x.2.2 ∧ x.2.2 ∈ tsupport (ψ x.2.1)
  have hlabels : ∀ a b x, a ≠ b → active a x → active b x →
      atlasPhaseLabel a ≠ atlasPhaseLabel b := by
    intro a b x hab ha hb
    exact atlas_distinct_labels_on_intersection p ψ hsource s hh hab ha.1.2 hb.1.2
  have hdata : ∀ a x, active a x → B x ≠ 0 ∧ ‖Ξ a x‖ ≤ 2*L*C ∧
      e*‖B x‖ ≤ ‖secondQuadratic (B x) (-(Ξ a x).2,(Ξ a x).1)‖ := by
    intro a x hx
    have hqa : x.2.2 ∈ tsupport (ψ a.1) :=
      refinedCutoff_tsupport_outer (p a.1) (ψ a.1) (s a.1) h a.2.1 hx.1.2
    have hap : x.2.2 ∈ (coordinateChart (p a.1)).source := by
      rw [coordinateChart_source]; exact hsource a.1 hqa
    have hjp : x.2.2 ∈ (coordinateChart (p x.2.1)).source := by
      rw [coordinateChart_source]; exact hsource x.2.1 hx.2
    have hc := hbound x.2.1 a.1 (coordinateChart (p x.2.1) x.2.2)
      ⟨x.2.2,⟨hx.2,hqa⟩,rfl⟩
    have hl := hlocal x.1 a x.2.2 hx.1
    have hm := actual_phase_margin_at (hG x.1) (p a.1) (p x.2.1)
      hjp hap (ξ a) hd hL hε hl.1 hc.1 hc.2 hl.2.1 hl.2.2
    refine ⟨hm.2.2.2,?_,hm.2.1⟩
    exact hm.1.trans (mul_le_mul_of_nonneg_left (hξ a) (by positivity))
  obtain ⟨w,hstock,hw,hcross⟩ := hweights B Ξ active hlabels hdata
  refine ⟨w,hstock,hw,?_⟩
  intro t a b j q hab ha hb hqj
  exact hcross a b (t,j,q) hab ⟨ha,hqj⟩ ⟨hb,hqj⟩

omit [T2Space M] [CompactSpace M] in
theorem atlas_phase_weight_constants (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    {ε C : ℝ} (hε : 0 < ε) (σ : Type*) :
    ∃ W κ : ℝ, 0 < W ∧ 0 < κ ∧
      ∀ h : ℝ, 0 < h → ∀ s : ι → Finset Index,
      ∀ ξ : AtlasCellPhase (ι := ι) → SmallModes.Base,
      (∀ a, ‖ξ a‖ ≤ C) →
      ∀ (G : σ → M → Space),
      (∀ t, ContMDiff planeModel spaceModel ∞ (G t)) →
      (∀ t a q, atlasActive p ψ s h a q →
        atlasGram (G t) (p a.1) q ≠ 0 ∧ atlasSecondTensor (G t) (p a.1) q ≠ 0 ∧
        ε*‖atlasSecondTensor (G t) (p a.1) q‖ ≤
          ‖secondQuadratic (atlasSecondTensor (G t) (p a.1) q) (-(ξ a).2,(ξ a).1)‖) →
      ∃ w : AtlasCellPhase (ι := ι) → ℝ, (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        ∀ (t : σ) (a b : AtlasCellPhase (ι := ι)) (j : ι) (q : M),
          a ≠ b → atlasActive p ψ s h a q → atlasActive p ψ s h b q → q ∈ tsupport (ψ j) →
          κ*‖atlasSecondTensor (G t) (p j) q‖ ≤
            ‖secondQuadratic (atlasSecondTensor (G t) (p j) q)
              (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
               (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
          κ*‖atlasSecondTensor (G t) (p j) q‖ ≤
            ‖secondQuadratic (atlasSecondTensor (G t) (p j) q)
              (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
               (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
                w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
          Good (atlasSecondTensor (G t) (p j) q)
            (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
             w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) ∧
          Good (atlasSecondTensor (G t) (p j) q)
            (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
             w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) := by
  obtain ⟨stock,W,κ,hW,hκ,hselect⟩ := atlas_phase_weight_constants_with_catalog
    p ψ hsource hcompact hε σ
  refine ⟨W,κ,hW,hκ,?_⟩
  intro h hh s ξ hξ G hG hlocal
  obtain ⟨w,_,hw,hm⟩ := hselect h hh s ξ hξ G hG hlocal
  exact ⟨w,hw,hm⟩

end ClosedSurfaceR4

end

end OAI
