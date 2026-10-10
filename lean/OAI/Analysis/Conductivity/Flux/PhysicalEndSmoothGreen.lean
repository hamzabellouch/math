import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalEndSmoothEnergy

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance physicalEndSmoothGreenMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance physicalEndSmoothGreenIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma fullAttachedEnd_smooth_green_pos (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : 0<a) (hlr : l<r) (hR : a*(r-l)=R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a l κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s l hφ))-
      κ*spectralGraphMean (torusRate s) (smoothCollarTrace s l hφ)+
      cylinderTerminalFlux s κ R f (smoothCollarTrace s r hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos ha (sub_pos.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a l t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg ha.le (sub_nonneg.mpr ht.1)
    · rw [←hR]; exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) ha.le
  have he := fullAttachedEnd_smooth_energy_pullback s hs f κ hφ ha.ne' hlr.le hRp.le hl hr hT
    (fun t ht => mul_pos ha (sub_pos.mpr ht.1))
  rw [he.2,mul_assoc,←mul_left_comm angularArea |a|,
    integral_affineEndCoordinates_pos ha hlr.le hT (by ring) hR hRp.le
      (sourceEndSmoothDensity_cylinder s hs f κ a⁻¹ l R hRp.le hφ).1,
    sourceEndSmoothDensity_green s hs f κ a⁻¹ l R hRp hφ]
  have hend : a⁻¹*R+l=r := by rw [←hR]; field_simp [ha.ne']; ring
  rw [hend]

lemma fullAttachedEnd_smooth_green_neg (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : a<0) (hlr : l<r) (hR : a*(l-r)=R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a r κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s r hφ))-
      κ*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)+
      cylinderTerminalFlux s κ R f (smoothCollarTrace s l hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos_of_neg_of_neg ha (sub_neg.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a r t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr ht.2)
    · rw [←hR]; exact mul_le_mul_of_nonpos_left (sub_le_sub_right ht.1 r) ha.le
  have he := fullAttachedEnd_smooth_energy_pullback s hs f κ hφ ha.ne hlr.le hRp.le hl hr hT
    (fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr ht.2))
  rw [he.2,mul_assoc,←mul_left_comm angularArea |a|,
    integral_affineEndCoordinates_neg ha hlr.le hT hR (by ring) hRp.le
      (sourceEndSmoothDensity_cylinder s hs f κ a⁻¹ r R hRp.le hφ).1,
    sourceEndSmoothDensity_green s hs f κ a⁻¹ r R hRp hφ]
  have hend : a⁻¹*R+r=l := by rw [←hR]; field_simp [ha.ne]; ring
  rw [hend]

end ScalarConductivity

end
end

end OAI
