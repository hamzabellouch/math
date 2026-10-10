import OAI.Geometry.RuledCovering.Main

namespace OAI

open Set MeasureTheory
open RuledApproximation
noncomputable section
namespace CylinderCovering.NilpotentRadialIntegral

def radialMap (z : Plane) : Plane := vec2 (z 0 * z 1) (z 1)

def parameterRegion (H : ℝ → ℝ) (ρ : ℝ) : Set Plane :=
  {z | z 0 ∈ Icc (-1 : ℝ) 1 ∧ z 1 ∈ Icc ρ (H (z 0))}

lemma radialMap_hasFDerivAt (z : Plane) :
    HasFDerivAt radialMap (matrixCLM (z 1) (z 0) 0 1) z := by
  have h0 := (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h := hasFDerivAt_vec2 (h0.mul h1) h1
  convert h using 1
  · rfl
  · ext w i
    fin_cases i <;> simp [matrixCLM, vec2]
    ring

lemma radialMap_det (z : Plane) : (matrixCLM (z 1) (z 0) 0 1).det = z 1 := by
  change LinearMap.det (matrixCLM (z 1) (z 0) 0 1).toLinearMap = z 1
  simp [matrixCLM_det]

lemma parameterRegion_isClosed (H : ℝ → ℝ) (hH : Continuous H) (ρ : ℝ) :
    IsClosed (parameterRegion H ρ) := by
  unfold parameterRegion
  have hp : Continuous (fun z : Plane => z 0) := by fun_prop
  have ht : Continuous (fun z : Plane => z 1) := by fun_prop
  exact (isClosed_Icc.preimage hp).inter
    ((isClosed_le continuous_const ht).inter (isClosed_le ht (hH.comp hp)))

lemma parameterRegion_isCompact (H : ℝ → ℝ) (hH : Continuous H) (ρ : ℝ) :
    IsCompact (parameterRegion H ρ) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image (hH.continuousOn : ContinuousOn H (Icc (-1 : ℝ) 1))
  have hbox : IsCompact ((fun q : ℝ × ℝ => vec2 q.1 q.2) ''
      (Icc (-1 : ℝ) 1 ×ˢ Icc ρ M)) := by
    apply (isCompact_Icc.prod isCompact_Icc).image
    unfold vec2
    fun_prop
  apply hbox.of_isClosed_subset (parameterRegion_isClosed H hH ρ)
  intro z hz
  refine ⟨(z 0, z 1), ⟨hz.1, hz.2.1, ?_⟩, vec2_coordinates z⟩
  exact hz.2.2.trans (hM ⟨z 0, hz.1, rfl⟩)

lemma radialMap_injOn {H : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) :
    InjOn radialMap (parameterRegion H ρ) := by
  intro x hx y hy heq
  have h1 := congrArg (fun z : Plane => z 1) heq
  have h0 := congrArg (fun z : Plane => z 0) heq
  change x 1 = y 1 at h1
  change x 0 * x 1 = y 0 * y 1 at h0
  have hx1 : x 1 ≠ 0 := ne_of_gt (hρ.trans_le hx.2.1)
  rw [← h1] at h0
  have hx0 := mul_right_cancel₀ hx1 h0
  ext i
  fin_cases i
  · exact hx0
  · exact h1

theorem radial_integral (H F : ℝ → ℝ) (hH : Continuous H) (hF : Continuous F)
    {ρ : ℝ} (hρ : 0 < ρ) (hHρ : ∀ p ∈ Icc (-1 : ℝ) 1, ρ ≤ H p) :
    (∫ b in radialMap '' parameterRegion H ρ, F (b 0 / b 1)) =
      ∫ p in Icc (-1 : ℝ) 1, ((H p) ^ 2 - ρ ^ 2) / 2 * F p := by
  have hcompact := parameterRegion_isCompact H hH ρ
  have hmeas := hcompact.measurableSet
  have hint : IntegrableOn (fun z : Plane => z 1 * F (z 0)) (parameterRegion H ρ) :=
    ContinuousOn.integrableOn_compact hcompact (by fun_prop)
  calc
    (∫ b in radialMap '' parameterRegion H ρ, F (b 0 / b 1)) =
        ∫ z in parameterRegion H ρ,
          |(matrixCLM (z 1) (z 0) 0 1).det| •
            F (radialMap z 0 / radialMap z 1) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hmeas
        (fun z _ => (radialMap_hasFDerivAt z).hasFDerivWithinAt)
        (radialMap_injOn hρ) _
    _ = ∫ z in parameterRegion H ρ, z 1 * F (z 0) := by
      apply setIntegral_congr_fun hmeas
      intro z hz
      have hz1 : 0 < z 1 := hρ.trans_le hz.2.1
      simp [radialMap_det, radialMap, abs_of_pos hz1, hz1.ne']
    _ = ∫ p in Icc (-1 : ℝ) 1, ∫ t in Icc ρ (H p), t * F p := by
      exact plane_setIntegral_vertical_interval hmeas hint measurableSet_Icc
        (fun _ => Iff.rfl)
    _ = ∫ p in Icc (-1 : ℝ) 1, ((H p) ^ 2 - ρ ^ 2) / 2 * F p := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro p hp
      dsimp only
      rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (hHρ p hp), integral_id]

end CylinderCovering.NilpotentRadialIntegral

end

end OAI
