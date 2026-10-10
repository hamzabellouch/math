import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSurfacePreparation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasNormalizationStability

namespace OAI

/-! The finite-point preparation on a closed surface: a spherical immersion
can be flattened at any finite set, with fixed C2 bounds and arbitrary C1 accuracy. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_spherical_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (c : P → A.centers) (G : M → Space),
        (∀ p, A.weight (c p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
        A.WeightedBound 1 1 ε (G-F) ∧ A.WeightedBound 1 2 D G ∧
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
            (chartAt Plane (c p : M) p) v w = 0 := by
  obtain ⟨Dq,hDq,hprep⟩ := A.finite_spherical_preparation_correction hF hunit
  obtain ⟨Cf,hCf,hFb⟩ := A.exists_weighted_bound 2 hF
  let C := max 1 (Cf+Dq)
  have hC : 1 ≤ C := le_max_left _ _
  obtain ⟨D,hD,hDb⟩ := A.radial_normalization_C2_budget C hC
  obtain ⟨εi,hεi,hIi⟩ := A.weighted_immersion_tolerance hF hImm
  refine ⟨D,hD,?_⟩
  intro P ε hε
  obtain ⟨δ,hδ,hstable⟩ := A.radial_normalization_C1_stability hF hunit (lt_min hε hεi)
  obtain ⟨c,Q,hc,hQ,hQ1,hQ2,hjets⟩ := hprep P δ hδ
  obtain ⟨hnorm,hclose⟩ := hstable Q hQ hQ1
  let G := radialNormalize ∘ (F+Q)
  have hG : ContMDiff planeModel spaceModel ∞ G := radial_normalization_smooth (hF.add hQ) hnorm
  have hunitG (p : M) : ‖G p‖ = 1 := by
    have hn : F p+Q p ≠ 0 := by
      intro hz
      have := hnorm p
      norm_num [hz] at this
    change ‖‖F p+Q p‖⁻¹ • (F p+Q p)‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]
  have hHbound : A.WeightedBound 1 2 C (F+Q) := by
    intro i
    have hb := (hFb i).add uniqueDiffOn_univ zero_le_one
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hQ).contDiffOn (hQ2 i)
    have he : (fun x => localize (i : M) (A.weight i) F x+localize (i : M) (A.weight i) Q x) =
        localize (i : M) (A.weight i) (F+Q) := (localize_add _ _ _ _).symm
    rw [he] at hb
    exact hb.mono_const (le_max_right _ _)
  refine ⟨c,G,hc,hG,hunitG,?_,?_,hDb (F+Q) (hF.add hQ) hnorm hHbound,hjets⟩
  · exact hIi G hG (fun i => (hclose i).mono_const (min_le_right _ _))
  · exact fun i => (hclose i).mono_const (min_le_left _ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
