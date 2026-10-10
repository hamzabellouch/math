import OAI.Geometry.SurfaceImmersion.Atlas.AtlasNormalizationBounds
import OAI.Geometry.SurfaceImmersion.Geometry.SafeNormalizationStability
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasUniformNorm
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! Small C1 perturbations of a spherical immersion remain small after
normalization, in the same fixed atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma normalized_difference_localization (i : A.centers) (F Q : M → Space)
    (hF : ∀ p, ‖F p‖ = 1) (hH : ∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖) :
    localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)-F) =
      fun x => (A.chartWeight i x)^2 •
        (safeRadialNormalize (A.vectorChartRead i F x+A.vectorChartRead i Q x)-
          safeRadialNormalize (A.vectorChartRead i F x)) := by
  have he : radialNormalize ∘ F = F := by
    funext p
    simp [Function.comp_apply,radialNormalize,hF p]
  have heF := A.normalized_localization_eq i F (fun p => by rw [hF]; norm_num)
  rw [he] at heF
  have heH := A.normalized_localization_eq i (F+Q) hH
  have heR : A.vectorChartRead i (F+Q) = A.vectorChartRead i F+A.vectorChartRead i Q :=
    localize_add _ _ _ _
  have hs : localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)-F) =
      localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)) - localize (i : M) (A.weight i) F := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx,smul_sub]
  rw [hs,heH,heF,heR]
  funext x
  simp only [Pi.sub_apply,Pi.add_apply,smul_sub]

omit [CompactSpace M] in
lemma weighted_perturbation_annulus {F Q : M → Space} (hF : ∀ p, ‖F p‖ = 1)
    {δ : ℝ} (hδ : (Fintype.card A.centers : ℝ)*δ ≤ 1/2)
    (hb : A.WeightedBound 1 1 δ Q) : ∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖ := by
  intro p
  have h0 : A.WeightedBound 1 0 δ Q := fun i => (hb i).mono_order (by omega)
  have hn := (A.weightedBound_uniform_norm h0 p).trans hδ
  have he : F p = (F p+Q p)-Q p := by abel
  have ht := norm_sub_le (F p+Q p) (Q p)
  rw [← he,hF] at ht
  linarith

theorem radial_normalization_C1_stability {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : M → Space, ContMDiff planeModel spaceModel ∞ Q →
      A.WeightedBound 1 1 δ Q →
      (∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖) ∧
      A.WeightedBound 1 1 ε (radialNormalize ∘ (F+Q)-F) := by
  classical
  have hlocal (i : A.centers) : ∃ δ : ℝ, 0 < δ ∧ ∀ Q : M → Space,
      ContMDiff planeModel spaceModel ∞ Q → A.WeightedBound 1 1 δ Q →
      (∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖) →
      WeightedEstimates.WeightedBound univ 1 1 ε
        (localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)-F)) := by
    obtain ⟨W,hW,hw⟩ := compact_smooth_bound ((A.chartWeight_smooth i).pow 2)
      (A.chartWeight_square_compact i) 1
    obtain ⟨C,hC,hCbound⟩ := compact_smooth_bound (A.vectorChartRead_smooth i hF)
      (localize_compact (i : M) (A.outer_support i) F) 1
    obtain ⟨η,hη,hstab⟩ := safe_normalization_C1_stability (A.vectorChartRead i F)
      (A.vectorChartRead_smooth i hF) C hC hCbound
      (div_pos hε (by positivity : 0 < 2*(W+1)))
    obtain ⟨R,hR,hr⟩ := A.vectorChartRead_bound (V := Space) i 1
    refine ⟨η/(R+1),div_pos hη (by positivity),?_⟩
    intro Q hQ hb hnorm
    have hread : WeightedEstimates.WeightedBound univ 1 1 η (A.vectorChartRead i Q) := by
      apply (hr Q 1 (η/(R+1)) zero_lt_one le_rfl (by positivity) hQ hb).mono_const
      have : R*(η/(R+1)) ≤ (R+1)*(η/(R+1)) := by gcongr; linarith
      have he : (R+1)*(η/(R+1)) = η := by field_simp
      rwa [he] at this
    have hc := hstab (A.vectorChartRead i Q) (A.vectorChartRead_smooth i hQ) hread
    rw [A.normalized_difference_localization i F Q hunit hnorm]
    apply (hw.smul_real uniqueDiffOn_univ zero_le_one hW (by positivity)
      ((A.chartWeight_smooth i).pow 2).contDiffOn
      ((safeRadialNormalize_smooth.comp ((A.vectorChartRead_smooth i hF).add
        (A.vectorChartRead_smooth i hQ))).sub
        (safeRadialNormalize_smooth.comp (A.vectorChartRead_smooth i hF))).contDiffOn hc).mono_const
    have he : 2*W*(ε/(2*(W+1))) ≤ 2*(W+1)*(ε/(2*(W+1))) := by gcongr; linarith
    simpa only [pow_one,mul_div_cancel₀ ε (by positivity : 2*(W+1) ≠ 0)] using he
  choose d hd hdb using hlocal
  obtain ⟨δ₁,hδ₁,_,hδ₁i⟩ := finite_positive_threshold d hd
  let δ := min (1/(2*((Fintype.card A.centers : ℝ)+1))) δ₁
  have hδ : 0 < δ := lt_min (by positivity) hδ₁
  have hδi (i : A.centers) : δ ≤ d i := (min_le_right _ _).trans (hδ₁i i)
  refine ⟨δ,hδ,?_⟩
  intro Q hQ hb
  have hnorm : ∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖ := by
    apply A.weighted_perturbation_annulus hunit _ hb
    have hδ0 : δ ≤ 1/(2*((Fintype.card A.centers : ℝ)+1)) := min_le_left _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2*((Fintype.card A.centers : ℝ)+1))).mp hδ0
    have hn : 0 ≤ (Fintype.card A.centers : ℝ) := by positivity
    nlinarith
  exact ⟨hnorm,fun i => hdb i Q hQ (fun j => (hb j).mono_const (hδi i)) hnorm⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
