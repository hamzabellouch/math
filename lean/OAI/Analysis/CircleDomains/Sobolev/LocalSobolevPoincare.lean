import OAI.Analysis.CircleDomains.Sobolev.RectangularPoincare
import OAI.Analysis.CircleDomains.Sobolev.LocalGradientIntegrability

namespace OAI

/-! Poincare for the precise continuous local W1,2 representative, with
its actual distributional partials and no additional line assumptions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_rectangular_poincare {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    let μ := (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))
    (⨍ p, |u (euclideanPlaneCoordinates.symm p)-
      (⨍ q, u (euclideanPlaneCoordinates.symm q) ∂μ)| ∂μ) ≤
    (b-a)*(⨍ p, |V (euclideanPlaneCoordinates.symm p) 0| ∂μ) +
    (d-c)*(⨍ p, |V (euclideanPlaneCoordinates.symm p) 1| ∂μ) := by
  dsimp only
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hμ : (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) =
      (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hcont : Continuous (fun p => u (euclideanPlaneCoordinates.symm p)) :=
    hu.comp euclideanPlaneCoordinates.symm.continuous
  have hf : Integrable (fun p => u (euclideanPlaneCoordinates.symm p))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [hμ]
    exact hcont.continuousOn.integrableOn_compact hK
  have hI (i : Fin 2) : Integrable (fun p => V (euclideanPlaneCoordinates.symm p) i)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [hμ]
    exact local_partial_coordinate_integrableOn hLp hK i
  apply rectangular_poincare hab hcd hf (hI 0) (hI 1)
  · filter_upwards [ae_restrict_of_ae (locally_sobolev_coordinate_fundamentalTheorem hu hw hLp 0)]
      with t ht
    intro s _ w _
    simpa only [physicalCoordinateLine, ite_true] using (ht s w).2
  · filter_upwards [ae_restrict_of_ae (locally_sobolev_coordinate_fundamentalTheorem hu hw hLp 1)]
      with s hs
    intro t _ w _
    simpa [physicalCoordinateLine] using (hs t w).2

end CircleDomainRigidity

end

end OAI
