import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildFullEndH1
import OAI.Analysis.Conductivity.Flux.PhysicalChildTensor

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceChild_integral (σ : ℝ) {D : Set (Fin 3 → ℝ)}
    (hD : MeasurableSet D) (g : (Fin 3 → ℝ) → ℝ) :
    (∫ y in sourceChildCoordinates σ '' D,g y)=
      ∫ y in D,sourceScale^3*g (sourceChildCoordinates σ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (fun x _ => (sourceChildCoordinates_hasFDeriv σ x).hasFDerivWithinAt)
    (sourceChildHomeomorph σ).injective.injOn g
  change (∫ y in sourceChildCoordinates σ '' D,g y)=
    ∫ y in D,|sourceChildDerivative.det| • g (sourceChildCoordinates σ y) at h
  simpa only [sourceChildDerivative_det,abs_neg,abs_pow,
    abs_of_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale]),smul_eq_mul] using h

lemma originalPiGradient_memLp_on_ball {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) (k : Fin 3) :
    MemLp (fun y => originalPiGradient u y k) 2 (volume.restrict D) := by
  have he := ballWholePiComponentCLM_ae_of_ae k.succ u.val
    (fun y => u.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl)
  apply MemLp.ae_eq ?_ ((Lp.memLp (ballWholePiComponentCLM k.succ u.val)).restrict D)
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem hD] with y hy hm
  rw [hy,ite_eq_left (hb y hm)]
  rfl

lemma originalPiGradient_eq_on_ball {D : Set (Fin 3 → ℝ)}
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1)
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → ∀ k,
      weakGradient u x k=G (WithLp.ofLp x) k) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient u y=G y := by
  have hh := (ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp he
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with y hy hm
  ext k
  exact hy (hb y hm) hm k

lemma sourceChild_image_ball (k : Fin 2) {D : Set (Fin 3 → ℝ)}
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ y∈sourceChildCoordinates (actualChildSign k) '' D,WithLp.toLp 2 y∈ball := by
  rintro _ ⟨y,hy,rfl⟩
  exact sourceChildEuclidean_ball k ⟨WithLp.toLp 2 y,hb y hy,rfl⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceChildTensorPush_entry_memLp (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (k : Fin 2) (i j : Fin 3) :
    MemLp (fun y => sourceChildTensorPush k (attachedCollarTensor s a) y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have hm := ((attachedCollarTensor_entry_memLp s ha (childAxis i) (childAxis j)).aestronglyMeasurable.comp_quasiMeasurePreserving
    (sourceChildInverse_quasi (actualChildSign k))).const_mul sourceScale⁻¹
  obtain ⟨B,hB,h⟩ := attachedFaceTensorList_bounded s ha
    (Finset.univ : Finset (Fin 4 × Fin 4)).toList
  apply memLp_top_of_bound hm (|sourceScale⁻¹| * B)
  apply ae_of_all
  intro y
  change ‖sourceScale⁻¹*attachedCollarTensor s a
    ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis i) (childAxis j)‖≤_
  rw [norm_mul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact ((norm_le_pi_norm _ (childAxis j)).trans
    (norm_le_pi_norm _ (childAxis i))).trans (h _)

lemma sourceChildTensorPush_weak_integrable (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0)
    (k : Fin 2) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (sourceChildTensorPush k (attachedCollarTensor s a) y*ᵥoriginalPiGradient v y))
      (volume.restrict D) := by
  have hrow (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3,
      sourceChildTensorPush k (attachedCollarTensor s a) y i j*originalPiGradient v y j)
        2 (volume.restrict D) := by
    apply memLp_finsetSum
    intro j _
    exact ((sourceChildTensorPush_entry_memLp s ha k i j).restrict D).mul (r := 2)
      (originalPiGradient_memLp_on_ball hD hb v j)
  change Integrable (fun y => ∑ i : Fin 3,originalPiGradient u y i*
    ∑ j : Fin 3,sourceChildTensorPush k (attachedCollarTensor s a) y i j*
      originalPiGradient v y j) _
  apply integrable_finsetSum
  intro i _
  exact (originalPiGradient_memLp_on_ball hD hb u i).integrable_mul (hrow i)

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem physicalChildFullEnd_weak_energy_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      (∀ᵐ x∂ballMeasure,
        (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈
          sourceClosedCollarBand (-centralThickness) 0 →
        weakValue w x=fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ
          ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
        ∀ q,weakGradient w x q=sourceScale⁻¹*
          fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ
            ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis q)) ∧
      (∀ (ψ : H1) (i j : Fin 4),
        Integrable (fun y => originalPiGradient w y ⬝ᵥ
          (sourceChildTensorPush k (attachedCollarTensor s a) y*ᵥoriginalPiGradient ψ y))
          (volume.restrict (sourceChildCoordinates (actualChildSign k) ''
            (sourceCollarPiece i j '' sourceExtendedBox (-centralThickness) 0))) ∧
        (∫ y in sourceChildCoordinates (actualChildSign k) ''
            (sourceCollarPiece i j '' sourceExtendedBox (-centralThickness) 0),
          originalPiGradient w y ⬝ᵥ
            (sourceChildTensorPush k (attachedCollarTensor s a) y*ᵥoriginalPiGradient ψ y))=
          ∫ x in sourceExtendedBox (-centralThickness) 0,
            |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
              (fullEndFlatCovector s (centralT s k.succ p) κ (a*(x 0-(-centralThickness)))
                  (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
                (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥ
                  (fun q => sourceScale*originalPiGradient ψ
                    (sourceChildCoordinates (actualChildSign k) (sourceCollarPiece i j x)) (childAxis q)))))) := by
  obtain ⟨w,hw,he⟩ := physicalChildFullEnd_H10 s hs ha k κ p
  have hlow : -(1:ℝ)/100≤-centralThickness := by norm_num [centralThickness]
  have hupp : (0:ℝ)≤1/100 := by norm_num
  have hb : ∀ y∈sourceClosedCollarBand (-centralThickness) 0,WithLp.toLp 2 y∈ball := by
    intro y hy
    exact sourceBand_mem_ball ⟨hlow.trans hy.1,hy.2.trans hupp⟩
  let D := (sourceChildHomeomorph (actualChildSign k)).symm ⁻¹'
    sourceClosedCollarBand (-centralThickness) 0
  have hDball : ∀ y∈D,WithLp.toLp 2 y∈ball := by
    intro y hy
    apply sourceChild_image_ball k hb y
    exact ⟨(sourceChildHomeomorph (actualChildSign k)).symm y,hy,
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y⟩
  have hjet := originalPiGradient_eq_on_ball hDball w
    (fun y q => sourceScale⁻¹*fullAttachedEndGradient s (centralT s k.succ p)
      a (-centralThickness) κ ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis q))
    (by filter_upwards [he] with x hx hm; exact (hx hm).2)
  refine ⟨w,hw,he,fun ψ i j => ?_⟩
  let E := sourceCollarPiece i j '' sourceExtendedBox (-centralThickness) 0
  have hE : MeasurableSet E := sourceCollarClosedPiece_measurable _ _ i j
  have hEsub := sourceCollarClosedPiece_subset hlow hupp i j
  have hchild : MeasurableSet (sourceChildCoordinates (actualChildSign k) '' E) :=
    (((isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).image
      (sourceChildCoordinates_contDiff (actualChildSign k)).continuous)).measurableSet
  constructor
  · exact sourceChildTensorPush_weak_integrable s ha.ne' k hchild
      (sourceChild_image_ball k (fun y hy => hb y (hEsub hy))) w ψ
  · calc
      _ = ∫ y in sourceChildCoordinates (actualChildSign k) '' E,
          (fun q => sourceScale⁻¹*fullAttachedEndGradient s (centralT s k.succ p)
            a (-centralThickness) κ ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis q)) ⬝ᵥ
              (sourceChildTensorPush k (attachedCollarTensor s a) y*ᵥoriginalPiGradient ψ y) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hjet,ae_restrict_mem hchild] with y hy hm
        apply congrArg (fun v => v ⬝ᵥ
          (sourceChildTensorPush k (attachedCollarTensor s a) y*ᵥoriginalPiGradient ψ y))
        apply hy
        rcases hm with ⟨z,hz,rfl⟩
        change (sourceChildHomeomorph (actualChildSign k)).symm
          (sourceChildHomeomorph (actualChildSign k) z)∈sourceClosedCollarBand (-centralThickness) 0
        rw [Homeomorph.symm_apply_apply]
        exact hEsub hz
      _ = ∫ y in E,fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ y ⬝ᵥ
          (attachedCollarTensor s a y*ᵥ(fun q => sourceScale*
            originalPiGradient ψ (sourceChildCoordinates (actualChildSign k) y) (childAxis q))) := by
        rw [sourceChild_integral (actualChildSign k) hE]
        apply integral_congr_ae
        apply ae_of_all
        intro y
        have hv : (sourceChildHomeomorph (actualChildSign k)).symm
            (sourceChildCoordinates (actualChildSign k) y)=y :=
          (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
        dsimp only
        rw [hv]
        exact sourceChildTensorPush_mixed k (attachedCollarTensor s a) y _ _
      _ = _ := fullAttachedEnd_vector_integral_open s hs (centralT s k.succ p) κ
        (fun y q => sourceScale*originalPiGradient ψ (sourceChildCoordinates (actualChildSign k) y) (childAxis q))
        ha.ne' i j hlow hupp (fun t ht => mul_pos ha (sub_pos.mpr ht.1))

end ScalarConductivity

end

end OAI
