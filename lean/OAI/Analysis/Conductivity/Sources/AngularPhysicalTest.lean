import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularGraph

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

theorem sourceAngularJet_attachedCovector {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {a : ℝ} (ha : a≠0) (b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    (fun k : Fin 3 => (sourceAngularJet f a⁻¹ b k.succ
      (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)=
      attachedFlatTestCovector f a i j x := by
  have h1 : |x 1|<1 := by exact hx.2.1
  have h2 : |x 2|<1 := by exact hx.2.2
  have ht : a⁻¹*(a*(x 0-b))+b=x 0 := by field_simp; ring
  rw [sourceAngularJet_face hf a⁻¹ b (a*(x 0-b)) i j ht h1 h2]
  have h := attachedFlatTestCovector_chain f ha i j (sourceCollarOpenBox_subset hx)
    ((hf.differentiable (by simp)).differentiableAt)
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  have h2' := congrFun h 2
  simp only [sourceFaceAngleMatrix,endAxialMatrix,mulVec_diagonal] at h0 h1' h2'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=
    1*(a*attachedFlatTestCovector f a i j x 0) at h0
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1=
    (2*Real.pi*faceRayDensity 1 i (x 1))*(1*attachedFlatTestCovector f a i j x 1) at h1'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2=
    (2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))*(1*attachedFlatTestCovector f a i j x 2) at h2'
  ext k
  fin_cases k
  · change a⁻¹*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=_
    rw [h0]; field_simp [ha]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))=_
    rw [h1']
    field_simp [(faceRayDensity_pos' (w:=1) (by norm_num) i (x 1)).ne',Real.pi_ne_zero]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))=_
    rw [h2']
    field_simp [(faceRayDensity_pos' (w:=sourceRadialWidth) (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)).ne',Real.pi_ne_zero]; rfl

end ScalarConductivity

end
end

end OAI
