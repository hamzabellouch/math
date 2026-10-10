import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalTensorBound
import OAI.Analysis.Conductivity.Sobolev.ParentFullEndH1

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

def originalPiGradient (u : H1) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => weakGradient u (WithLp.toLp 2 y) k

lemma originalPiGradient_memLp {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : D⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) (u : H1) (k : Fin 3) :
    MemLp (fun y => originalPiGradient u y k) 2 (volume.restrict D) := by
  have he := ballWholePiComponentCLM_ae_of_ae k.succ u.val
    (fun y => u.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl)
  apply MemLp.ae_eq ?_ ((Lp.memLp (ballWholePiComponentCLM k.succ u.val)).restrict D)
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem hD] with y hy hm
  rw [hy,ite_eq_left (sourceBand_mem_ball (hb hm))]
  rfl

lemma sourceCollarClosedPiece_subset {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (i j : Fin 4) :
    sourceCollarPiece i j '' sourceExtendedBox l r ⊆ sourceClosedCollarBand l r := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  exact (subset_iUnion_of_subset i (subset_iUnion_of_subset j (Subset.rfl)))

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

lemma attachedCartesianMatrix_transport_vector {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (v : Fin 3 → ℝ) :
    attachedCartesianMatrix a i j x*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥv)=v := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]

lemma fullAttachedEnd_vector_energy (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (v : Fin 3 → ℝ)
    {a b : ℝ} (ha : a≠0) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    |(sourceCollarJacobian i j x).det| *
      (fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x) ⬝ᵥ
        (attachedCollarTensor s a (sourceCollarPiece i j x)*ᵥv))=
      |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
          (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥv))) := by
  have hv := attachedCartesianMatrix_transport_vector ha i j (sourceCollarOpenBox_subset hx) v
  have h := attachedFlatTensor_energy_density s ha i j (sourceCollarOpenBox_subset hx)
    (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)))
    ((attachedCartesianMatrix a i j x)⁻¹*ᵥv)
  rw [hv,←fullAttachedEndGradient_transport s hs f a b κ i j hx ht,
    ←attachedCollarTensor_open s a i j hx] at h
  exact h

lemma fullAttachedEnd_vector_integral (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    {a b l r : ℝ} (ha : a≠0) (i j : Fin 4)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (ht : ∀ t∈Icc l r,0<a*(t-b)) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
      fullAttachedEndGradient s f a b κ y ⬝ᵥ (attachedCollarTensor s a y*ᵥG y))=
      ∫ x in sourceExtendedBox l r,
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
            (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥG (sourceCollarPiece i j x)))) := by
  rw [sourceExtended_integral i j hl hr]
  apply integral_congr_ae
  filter_upwards [sourceExtendedBox_open_ae hl hr,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  simp only [smul_eq_mul]
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det]
  exact fullAttachedEnd_vector_energy s hs f κ _ ha i j hx (ht (x 0) (mem_sourceExtendedBox.mp hm).1)

lemma attachedCollarTensor_entry_memLp (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 3) : MemLp (fun y => attachedCollarTensor s a y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have hA := attachedCollarTensor_memLp_top s ha
  apply hA.of_le
  · exact (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hA.aestronglyMeasurable)
  · exact ae_of_all _ (fun y => (norm_le_pi_norm (attachedCollarTensor s a y i) j).trans
      (norm_le_pi_norm (attachedCollarTensor s a y) i))

lemma attachedCollarTensor_weak_integrable (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : D⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥoriginalPiGradient v y)) (volume.restrict D) := by
  have hrow (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3,
      attachedCollarTensor s a y i j*originalPiGradient v y j) 2 (volume.restrict D) := by
    apply memLp_finsetSum
    intro j _
    exact ((attachedCollarTensor_entry_memLp s ha i j).restrict D).mul (r := 2)
      (originalPiGradient_memLp hD hb v j)
  change Integrable (fun y => ∑ i : Fin 3,originalPiGradient u y i*
    ∑ j : Fin 3,attachedCollarTensor s a y i j*originalPiGradient v y j) _
  apply integrable_finsetSum
  intro i _
  exact (originalPiGradient_memLp hD hb u i).integrable_mul (hrow i)

lemma originalPiGradient_eq_on {D : Set (Fin 3 → ℝ)}
    (hb : D⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) (u : H1)
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → ∀ k,
      weakGradient u x k=G (WithLp.ofLp x) k) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient u y=G y := by
  have hh := (ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp he
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with y hy hm
  ext k
  exact hy (sourceBand_mem_ball (hb hm)) hm k

theorem fullAttachedEnd_weak_energy_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {a b l₀ l r r₀ R : ℝ} (ha : a≠0) (hR : 0≤R)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l≤r) (hl : l₀<l) (hr : r<r₀)
    (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100)
    (hT : ∀ t∈Icc l₀ r₀,affineEndTime a b t∈Icc 0 R)
    (hpos : ∀ t∈Icc l₀ r₀,0<a*(t-b)) :
    ∃ w : H1,w∈H10 ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand l r →
        weakValue w x=fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
        ∀ k,weakGradient w x k=fullAttachedEndGradient s f a b κ (WithLp.ofLp x) k) ∧
      (∀ (ψ : H1) (i j : Fin 4),
        Integrable (fun y => originalPiGradient w y ⬝ᵥ
          (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y))
          (volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r)) ∧
        (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
          originalPiGradient w y ⬝ᵥ (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y))=
          ∫ x in sourceExtendedBox l r,
            |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
              (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
                (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥ
                  originalPiGradient ψ (sourceCollarPiece i j x))))) := by
  obtain ⟨w,hw,he⟩ := fullAttachedEnd_neighborhood_H10 s hs f κ ha hR hb hlr hl hr hl₀ hr₀ hT hpos
  have hlow := hl₀.trans hl.le
  have hupp := hr.le.trans hr₀
  have hband : sourceClosedCollarBand l r⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun _ hy => ⟨hlow.trans hy.1,hy.2.trans hupp⟩
  have hjet := originalPiGradient_eq_on hband w (fullAttachedEndGradient s f a b κ)
    (by filter_upwards [he] with x hx hm; exact (hx hm).2)
  refine ⟨w,hw,he,fun ψ i j => ⟨?_,?_⟩⟩
  · exact attachedCollarTensor_weak_integrable s ha (sourceCollarClosedPiece_measurable l r i j)
      ((sourceCollarClosedPiece_subset hlow hupp i j).trans hband) w ψ
  · calc
      _ = ∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,
          fullAttachedEndGradient s f a b κ y ⬝ᵥ (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hjet,
          ae_restrict_mem (sourceCollarClosedPiece_measurable l r i j)] with y hy hm
        rw [hy (sourceCollarClosedPiece_subset hlow hupp i j hm)]
      _ = _ := fullAttachedEnd_vector_integral s hs f κ (originalPiGradient ψ) ha i j hlow hupp
        (fun t ht => hpos t ⟨hl.le.trans ht.1,ht.2.trans hr.le⟩)

end ScalarConductivity

end

end OAI
