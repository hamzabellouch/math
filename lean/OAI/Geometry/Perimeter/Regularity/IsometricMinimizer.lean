import OAI.Geometry.Perimeter.Regularity.PlaneLaplacian

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

def isometricPullbackField (e : Euc n ≃ₗᵢ[ℝ] Euc n) (V : Euc n → Euc n) : Euc n → Euc n :=
  fun x ↦ e.symm (V (e x))

theorem divergence_isometricPullback (e : Euc n ≃ₗᵢ[ℝ] Euc n)
    {V : Euc n → Euc n} (hV : Differentiable ℝ V) (x : Euc n) :
    divergence (isometricPullbackField e V) x = divergence V (e x) := by
  have hd : fderiv ℝ (isometricPullbackField e V) x =
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ V (e x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap) :=
    (e.symm.hasFDerivAt.comp x ((hV (e x)).hasFDerivAt.comp x e.hasFDerivAt)).fderiv
  rw [divergence_eq_trace,hd,divergence_eq_trace]
  change LinearMap.trace ℝ (Euc n) (e.symm.toLinearMap.comp
    ((fderiv ℝ V (e x)).toLinearMap.comp e.toLinearMap)) = _
  rw [LinearMap.trace_comp_comm',LinearMap.comp_assoc]
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact e.apply_symm_apply z
  rw [he,LinearMap.comp_id]

theorem admissible_isometricPullback (e : Euc n ≃ₗᵢ[ℝ] Euc n)
    {V : Euc n → Euc n} {U : Set (Euc n)} (hV : PerimeterAdmissible U V) :
    PerimeterAdmissible (e ⁻¹' U) (isometricPullbackField e V) := by
  refine ⟨e.symm.contDiff.comp (hV.1.comp e.contDiff),
    (hV.2.1.comp_homeomorph e.toHomeomorph).comp_left (map_zero e.symm), ?_, ?_⟩
  · have hs : tsupport (isometricPullbackField e V) ⊆ tsupport (V ∘ e) := by
      apply closure_mono
      intro x hx
      contrapose! hx
      simp only [Function.mem_support, not_not] at hx ⊢
      change e.symm (V (e x))=0
      rw [show V (e x)=0 from hx,map_zero]
    exact hs.trans ((tsupport_comp_subset_preimage V e.continuous).trans
      (preimage_mono hV.2.2.1))
  · intro x
    change ‖e.symm (V (e x))‖≤1
    rw [e.symm.norm_map]
    exact hV.2.2.2 _

theorem integral_divergence_isometricPullback (e : Euc n ≃ₗᵢ[ℝ] Euc n)
    (E : Set (Euc n)) {V : Euc n → Euc n} (hV : Differentiable ℝ V) :
    (∫ x in e ⁻¹' E, divergence (isometricPullbackField e V) x) =
      ∫ x in E, divergence V x := by
  simp_rw [divergence_isometricPullback e hV]
  exact e.measurePreserving.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding _ _

theorem perimeter_isometric_preimage (e : Euc n ≃ₗᵢ[ℝ] Euc n) (E U : Set (Euc n)) :
    perimeter (e ⁻¹' E) (e ⁻¹' U)=perimeter E U := by
  have hle (d : Euc n ≃ₗᵢ[ℝ] Euc n) (A B : Set (Euc n)) :
      perimeter A B ≤ perimeter (d ⁻¹' A) (d ⁻¹' B) := by
    rw [perimeter_eq_iSup_tests]
    apply iSup_le; intro V
    apply iSup_le; intro hV
    rw [← integral_divergence_isometricPullback d A (hV.1.differentiable (by simp))]
    rw [perimeter_eq_iSup_tests]
    exact le_iSup_of_le (isometricPullbackField d V)
      (le_iSup_of_le (admissible_isometricPullback d hV) le_rfl)
  apply le_antisymm
  · simpa only [← preimage_comp,Function.comp_def,e.apply_symm_apply,preimage_id'] using
      hle e.symm (e ⁻¹' E) (e ⁻¹' U)
  · exact hle e E U

theorem perimeterSupport_isometric_preimage (e : Euc n ≃ₗᵢ[ℝ] Euc n) (E : Set (Euc n)) :
    perimeterSupport (e ⁻¹' E)=e ⁻¹' perimeterSupport E := by
  ext x
  change (∀ r, 0<r → 0<perimeter (e ⁻¹' E) (Metric.ball x r)) ↔
    ∀ r, 0<r → 0<perimeter E (Metric.ball (e x) r)
  have he (r : ℝ) : e ⁻¹' Metric.ball (e x) r=Metric.ball x r := by
    rw [e.preimage_ball,e.symm_apply_apply]
  simp_rw [← he,perimeter_isometric_preimage]

theorem locally_minimizing_isometric_preimage (e : Euc n ≃ₗᵢ[ℝ] Euc n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) :
    IsLocallyPerimeterMinimizing (e ⁻¹' E) := by
  have hball (x : Euc n) (r : ℝ) : e ⁻¹' Metric.ball (e x) r=Metric.ball x r := by
    rw [e.preimage_ball,e.symm_apply_apply]
  refine ⟨hmin.1.preimage e.continuous.measurable, ?_, ?_⟩
  · intro x r hr
    rw [← hball,perimeter_isometric_preimage]
    exact hmin.2.1 _ r hr
  · intro x r hr F hF hcF hsF
    let G := e.symm ⁻¹' F
    have hG : MeasurableSet G := hF.preimage e.symm.continuous.measurable
    have he : e.symm ⁻¹' (e ⁻¹' E)=E := by ext y; simp
    have hg : e ⁻¹' G=F := by ext y; simp [G]
    have hcl : closure (symmDiff E G)=e.symm ⁻¹' closure (symmDiff (e ⁻¹' E) F) := by
      change _ = e.symm.toHomeomorph ⁻¹' _
      rw [e.symm.toHomeomorph.preimage_closure,preimage_symmDiff]
      change _ = closure (symmDiff (e.symm ⁻¹' (e ⁻¹' E)) G)
      rw [he]
    have hcG : IsCompact (closure (symmDiff E G)) := by
      rw [hcl]
      exact e.symm.toHomeomorph.isCompact_preimage.mpr hcF
    have hsG : closure (symmDiff E G) ⊆ Metric.ball (e x) r := by
      intro y hy
      rw [hcl] at hy
      have hh := hsF hy
      rw [← hball] at hh
      simpa only [mem_preimage,e.apply_symm_apply] using hh
    have hcmp := hmin.2.2 (e x) r hr G hG hcG hsG
    rw [← hball,perimeter_isometric_preimage,← hg,perimeter_isometric_preimage]
    exact hcmp

end RPISingularHarnack

end

end OAI
