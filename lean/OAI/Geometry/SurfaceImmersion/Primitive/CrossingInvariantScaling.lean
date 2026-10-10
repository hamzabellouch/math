import OAI.Geometry.SurfaceImmersion.Primitive.CrossingChoiceScaling

namespace OAI

/-! Both ordered crossing invariants scale by the positive product of
squared changes in the two tangent directions. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma normalize_pos_smul (v : Vec) {c : ℝ} (hc : 0 < c) :
    VelocityFrame.normalize (c • v) = VelocityFrame.normalize v := by
  have hs : Real.sqrt ((c • v) ⬝ᵥ (c • v)) = c*Real.sqrt (v ⬝ᵥ v) := by
    simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
    rw [← mul_assoc,← pow_two,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le]
  simp only [VelocityFrame.normalize,hs,mul_inv_rev,smul_smul]
  congr 1
  field_simp

lemma realSecondForm_smul_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (r s : ℝ) (v w p : Base) :
    realSecondForm F (r • v) (s • w) p = (r*s) • realSecondForm F v w p := by
  rw [realSecondForm_bilinear hF,realSecondForm_bilinear hF]
  ext j
  simp [realSecondTensor]
  ring

lemma gramDet_smul_directions (X Y : Vec) (r s : ℝ) :
    NormalFrame.gramDet (r • X) (s • Y) = r^2*s^2*NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

lemma orderedCrossing_smul_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {r s : ℝ} (hr : r ≠ 0) (v w p : Base) (κ : ℝ) :
    orderedCrossing F (r • v) (s • w) p κ = r^2*s^2*orderedCrossing F v w p κ := by
  have hd (t : ℝ) (u : Base) : coordDeriv (t • u) F p = t • coordDeriv u F p := by
    simp [coordDeriv]
  simp only [orderedCrossing,realSecondForm_smul_directions hF,
    show r*r=r^2 by ring,normalize_pos_smul _ (sq_pos_of_ne_zero hr),
    hd,gramDet_smul_directions,smul_dotProduct,smul_eq_mul]
  ring

lemma orderedCrossing_firstSlope {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) (κ : ℝ) (hv : v.1 ≠ 0) (hw : w.1 ≠ 0) :
    orderedCrossing F v w p κ = v.1^2*w.1^2*
      orderedCrossing F (1,v.2/v.1) (1,w.2/w.1) p κ := by
  have hh (u : Base) (hu : u.1 ≠ 0) : u.1 • ((1,u.2/u.1) : Base) = u := by
    apply Prod.ext
    · simp
    · change u.1*(u.2/u.1)=u.2
      field_simp
  convert orderedCrossing_smul_directions hF hv ((1,v.2/v.1) : Base)
    ((1,w.2/w.1) : Base) p κ (s := w.1) using 1
  rw [hh v hv,hh w hw]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
