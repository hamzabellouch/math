import OAI.Geometry.SurfaceImmersion.Geometry.SignedDiagonalFilling

namespace OAI

/-! An actual normalized two-zero field, rather than an assumed standard
model, admits a relative rank-two frame filling near its connecting interval. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem normalized_pair_frame_filling {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q : ℝ} (hpq : p < q) {W : Set ℝ} (hW : IsOpen W) (hKW : Icc p q ⊆ W)
    (haxis : ∀ t ∈ W, G (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hIp : Function.Bijective (fderiv ℝ G (crosscapAxis p)))
    (hIq : Function.Bijective (fderiv ℝ G (crosscapAxis q)))
    {U : Set Base} (hU : IsOpen U) (hAU : ∀ t ∈ Icc p q, crosscapAxis t ∈ U) :
    ∃ V : Set Base, IsOpen V ∧ V ⊆ U ∧
      (∀ t ∈ Icc p q, crosscapAxis t ∈ V) ∧ HasRelativeDefectFilling G V := by
  let a := fderiv ℝ G (crosscapAxis p) (![1,0] : Base) 1
  let b := fderiv ℝ G (crosscapAxis q) (![1,0] : Base) 1
  let F := normalizedLinearModel G p q
  let D := diagonalDefectModel (endpointSignModel p q a b) p q
  have hF : ContDiff ℝ ∞ F := normalizedLinearModel_smooth hG p q
  have hD : ContDiff ℝ ∞ D := diagonalDefectModel_smooth (endpointSignModel_smooth p q a b) p q
  have ha : a ≠ 0 := normalized_axis_transverse_nonzero hG.contDiffAt hW
    (hKW (left_mem_Icc.mpr hpq.le)) haxis hIp
  have hb : b ≠ 0 := normalized_axis_transverse_nonzero hG.contDiffAt hW
    (hKW (right_mem_Icc.mpr hpq.le)) haxis hIq
  have hprod : ∀ t, 0 < (fderiv ℝ G (crosscapAxis t) (![1,0] : Base) 1)*
      endpointSignModel p q a b t →
      0 < (fderiv ℝ F (crosscapAxis t) (![1,0] : Base) 1)*
        (fderiv ℝ D (crosscapAxis t) (![1,0] : Base) 1) := by
    intro t ht
    dsimp [F,D]
    rw [normalizedLinearModel_fderiv_axis hG,diagonalDefectModel_fderiv_axis
      (endpointSignModel_smooth p q a b)]
    simpa [normalTransverse,triangularPlaneJet] using ht
  obtain ⟨r₁,O₁,hr₁,hO₁,hrect₁,hz₁⟩ := linearDefectHomotopy_two_zeros hG hpq hW hKW haxis hIp hIq
  obtain ⟨r₂,O₂,hr₂,hO₂,hrect₂,hz₂⟩ := planeDefectInterpolation_two_zeros hF hD hpq
    isOpen_univ (subset_univ _) (fun t _ => normalizedLinearModel_axis G p q t)
    (fun t _ => diagonalDefectModel_axis _ p q t)
    (hprod p (endpointSignModel_left_mul_pos hpq.ne ha))
    (hprod q (endpointSignModel_right_mul_pos hpq.ne hb))
  let V := U ∩ O₁ ∩ O₂
  have hV : IsOpen V := (hU.inter hO₁).inter hO₂
  have hAV : ∀ t ∈ Icc p q, crosscapAxis t ∈ V := by
    intro t ht
    refine ⟨⟨hAU t ht,?_⟩,?_⟩ <;> rw [crosscapAxis_apply]
    · exact hrect₁ 0 ⟨by linarith,by linarith⟩ t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    · exact hrect₂ 0 ⟨by linarith,by linarith⟩ t ⟨by linarith [ht.1],by linarith [ht.2]⟩
  let Z : Set Base := {crosscapAxis p,crosscapAxis q}
  have hZ : IsCompact Z := isCompact_singleton.insert _
  have hZV : Z ⊆ V := by
    rintro x (rfl | rfl)
    · exact hAV p (left_mem_Icc.mpr hpq.le)
    · exact hAV q (right_mem_Icc.mpr hpq.le)
  have hDF : HasRelativeDefectFilling D V := signed_diagonal_filling hpq hV hAV
  have hP1 : planeDefectInterpolation F D 1 = D := by
    funext x
    simp [planeDefectInterpolation]
  have hP0 : planeDefectInterpolation F D 0 = F := by
    funext x
    simp [planeDefectInterpolation]
  have hL1 : linearDefectHomotopy G p q 1 = F := by
    funext x
    simp [linearDefectHomotopy,F]
  have hL0 : linearDefectHomotopy G p q 0 = G := by
    funext x
    simp [linearDefectHomotopy]
  have hFfill : HasRelativeDefectFilling F V := by
    have h := relativeDefectFilling_homotopy (planeDefectInterpolation_smooth hF hD) hV hZ hZV
      (fun s hs x hx hnot he => hnot (by
        have hz := (hz₂ s hs x hx.2).mp he
        simpa only [Z,mem_insert_iff,mem_singleton_iff] using hz))
      (by rw [hP1]; exact hDF)
    rwa [hP0] at h
  have hGfill : HasRelativeDefectFilling G V := by
    have h := relativeDefectFilling_homotopy (linearDefectHomotopy_smooth hG p q) hV hZ hZV
      (fun s hs x hx hnot he => hnot (by
        have hz := (hz₁ s hs x hx.1.2).mp he
        simpa only [Z,mem_insert_iff,mem_singleton_iff] using hz))
      (by rw [hL1]; exact hFfill)
    rwa [hL0] at h
  exact ⟨V,hV,fun _ hx => hx.1.1,hAV,hGfill⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
