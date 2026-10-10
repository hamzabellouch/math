import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildFullEndH1

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

theorem childFullEnd_weak_energy_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
        weakValue w x=fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) ∧
        ∀ q,weakGradient w x q=fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) q) ∧
      (∀ (ψ : H1) (i j : Fin 4),
        Integrable (fun y => originalPiGradient w y ⬝ᵥ
          (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y))
          (volume.restrict (sourceCollarPiece i j '' sourceExtendedBox (-centralThickness) 0)) ∧
        (∫ y in sourceCollarPiece i j '' sourceExtendedBox (-centralThickness) 0,
          originalPiGradient w y ⬝ᵥ (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y))=
          ∫ x in sourceExtendedBox (-centralThickness) 0,
            |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
              (fullEndFlatCovector s (centralT s k.succ p) κ (a*(x 0-(-centralThickness)))
                  (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
                (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥ
                  originalPiGradient ψ (sourceCollarPiece i j x))))) := by
  obtain ⟨w,hw,he⟩ := childFullEnd_H10 s hs ha k κ p
  have hlow : -(1:ℝ)/100≤-centralThickness := by norm_num [centralThickness]
  have hupp : (0:ℝ)≤1/100 := by norm_num
  have hband : sourceClosedCollarBand (-centralThickness) 0⊆
      sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun _ hy => ⟨hlow.trans hy.1,hy.2.trans hupp⟩
  have hjet := originalPiGradient_eq_on hband w
    (fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ)
    (by filter_upwards [he] with x hx hm; exact (hx hm).2)
  refine ⟨w,hw,he,fun ψ i j => ⟨?_,?_⟩⟩
  · exact attachedCollarTensor_weak_integrable s ha.ne'
      (sourceCollarClosedPiece_measurable (-centralThickness) 0 i j)
      ((sourceCollarClosedPiece_subset hlow hupp i j).trans hband) w ψ
  · calc
      _ = ∫ y in sourceCollarPiece i j '' sourceExtendedBox (-centralThickness) 0,
          fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ y ⬝ᵥ
            (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hjet,
          ae_restrict_mem (sourceCollarClosedPiece_measurable (-centralThickness) 0 i j)] with y hy hm
        rw [hy (sourceCollarClosedPiece_subset hlow hupp i j hm)]
      _ = _ := fullAttachedEnd_vector_integral_open s hs (centralT s k.succ p) κ
        (originalPiGradient ψ) ha.ne' i j hlow hupp
        (fun t ht => mul_pos ha (sub_pos.mpr ht.1))

end ScalarConductivity

end

end OAI
