import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialCompactness
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialGreen

namespace OAI

/-! Density of cusp test functions upgrades their precompactness to
compactness of the completed form inclusion and its Green operator. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRadialEnergyTest_smul (A : ℝ) (c : ℂ) (f : cubicThetaRadialTests) :
    cubicThetaRadialEnergyTest A (c • f)=c • cubicThetaRadialEnergyTest A f := by
  apply Subtype.ext
  exact (cubicThetaRadialGraph A).map_smul c f

theorem cubicThetaRadialInclusion_compact {A : ℝ} (hA : 0<A) :
    IsCompactOperator (cubicThetaRadialInclusion A) := by
  let K := closure (Set.range (fun f : CubicThetaRadialUnitTests A =>
    cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val)))
  have hK : IsCompact K := cubicThetaRadial_unit_precompact hA
  let K₂ := (fun x : CubicThetaRadialL2 => (2:ℂ) • x) '' K
  have hK₂ : IsCompact K₂ := hK.image (continuous_id.const_smul (2:ℂ))
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (cubicThetaRadialInclusion A).toLinearMap (by norm_num : (0:ℝ)<1)).mpr
  refine ⟨K₂,hK₂,?_⟩
  rintro y ⟨u,hu,rfl⟩
  have hnormu : ‖(u:CubicThetaRadialAmbient)‖ ≤ 1 := by simpa using hu
  rw [← hK₂.isClosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hδ : 0 < min 1 ε := lt_min (by norm_num) hε
  obtain ⟨v,hv,hclose⟩ := Metric.mem_closure_iff.mp u.property (min 1 ε) hδ
  obtain ⟨f,rfl⟩ := hv
  have hnormf : ‖cubicThetaRadialGraph A f‖<2 := by
    have htri : ‖cubicThetaRadialGraph A f‖ ≤
        ‖cubicThetaRadialGraph A f-(u:CubicThetaRadialAmbient)‖+‖(u:CubicThetaRadialAmbient)‖ := by
      calc
        _ = ‖(cubicThetaRadialGraph A f-(u:CubicThetaRadialAmbient))+(u:CubicThetaRadialAmbient)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hc : ‖cubicThetaRadialGraph A f-(u:CubicThetaRadialAmbient)‖<1 := by
      rw [← dist_eq_norm,dist_comm]
      exact hclose.trans_le (min_le_left _ _)
    linarith
  let g : cubicThetaRadialTests := (1/2:ℂ) • f
  have hg : ‖cubicThetaRadialGraph A g‖ ≤ 1 := by
    dsimp [g]
    rw [map_smul,norm_smul]
    norm_num
    linarith
  let g₁ : CubicThetaRadialUnitTests A := ⟨g,hg⟩
  have hy : (2:ℂ) • cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A g)=
      cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f) := by
    dsimp [g]
    rw [cubicThetaRadialEnergyTest_smul,map_smul,smul_smul]
    norm_num
  refine ⟨(2:ℂ) • cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A g),?_,?_⟩
  · exact ⟨cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A g),
      subset_closure ⟨g₁,rfl⟩,rfl⟩
  · rw [hy]
    have hd := cubicThetaRadialCoordinate_bound A 0 (u-cubicThetaRadialEnergyTest A f)
    have he : ‖u-cubicThetaRadialEnergyTest A f‖=
        ‖(u:CubicThetaRadialAmbient)-cubicThetaRadialGraph A f‖ := rfl
    rw [he,map_sub] at hd
    have hd' : dist (cubicThetaRadialInclusion A u)
        (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f)) ≤
        dist (u:CubicThetaRadialAmbient) (cubicThetaRadialGraph A f) := by
      simpa only [dist_eq_norm] using hd
    exact hd'.trans_lt (hclose.trans_le (min_le_right _ _))

theorem cubicThetaRadialGreen_compact {A : ℝ} (hA : 0<A) :
    IsCompactOperator (cubicThetaRadialGreen A) :=
  (cubicThetaRadialInclusion_compact hA).comp_clm (cubicThetaRadialInclusion A).adjoint

end CubicFirstMoment

end

end OAI
