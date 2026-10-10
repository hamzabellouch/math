import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateGauss
import OAI.Geometry.SurfaceImmersion.Geometry.OrderedBoundaryInvariant

namespace OAI

/-! The boundary Gauss inequality used when matching the interior and
exterior preferred normals. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open SmallModes RealModes NormalFrame

lemma dot_square_le_self_of_unit (W n : Vec) (hn : n ⬝ᵥ n = 1) :
    (W ⬝ᵥ n)^2 ≤ W ⬝ᵥ W := by
  have h : 0 ≤ (W-(W ⬝ᵥ n) • n) ⬝ᵥ (W-(W ⬝ᵥ n) • n) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  simp only [sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,hn,dotProduct_comm n W] at h
  nlinarith

lemma secondForm_gauss_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) :
    realSecondForm F v v p ⬝ᵥ realSecondForm F w w p -
      realSecondForm F v w p ⬝ᵥ realSecondForm F v w p =
    (v.1*w.2-v.2*w.1)^2 *
      (realSecondForm F dx dx p ⬝ᵥ realSecondForm F dy dy p -
        realSecondForm F dx dy p ⬝ᵥ realSecondForm F dx dy p) := by
  conv_lhs =>
    simp only [realSecondForm_bilinear hF v v,realSecondForm_bilinear hF w w,
      realSecondForm_bilinear hF v w]
  simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    dotProduct_comm (realSecondForm F dy dy p) (realSecondForm F dx dx p),
    dotProduct_comm (realSecondForm F dx dy p) (realSecondForm F dx dx p),
    dotProduct_comm (realSecondForm F dy dy p) (realSecondForm F dx dy p)]
  ring

lemma orderedCrossing_le_pure_pairing {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (kappa : ℝ)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hA : realSecondForm F v v p ≠ 0)
    (hk : coordinateGauss (realMetric F dx dx) (realMetric F dx dy)
      (realMetric F dy dy) p = kappa*gramDet (coordDeriv dx F p) (coordDeriv dy F p)) :
    orderedCrossing F v w p kappa ≤
      realSecondForm F v v p ⬝ᵥ realSecondForm F w w p := by
  have hg := secondForm_gauss_directions hF p v w
  rw [gauss_metric_identity hF p hD,hk] at hg
  have hgram : gramDet (coordDeriv v F p) (coordDeriv w F p) =
      (v.1*w.2-v.2*w.1)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [coordDeriv_eq_basis F v,coordDeriv_eq_basis F w,gramDet_change_basis]
  have hp := dot_square_le_self_of_unit (realSecondForm F v w p)
    (normalize (realSecondForm F v v p)) (normalize_unit hA)
  unfold orderedCrossing
  rw [hgram]
  nlinarith

lemma orderedCrossing_pos_pure_pairing {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (kappa : ℝ)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hA : realSecondForm F v v p ≠ 0)
    (hk : coordinateGauss (realMetric F dx dx) (realMetric F dx dy)
      (realMetric F dy dy) p = kappa*gramDet (coordDeriv dx F p) (coordDeriv dy F p))
    (hQ : 0 < orderedCrossing F v w p kappa) :
    0 < realSecondForm F w w p ⬝ᵥ normalize (realSecondForm F v v p) := by
  have hp := hQ.trans_le (orderedCrossing_le_pure_pairing hF p v w kappa hD hA hk)
  rw [normalize,dotProduct_smul,dotProduct_comm (realSecondForm F w w p)]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (dot_self_pos hA))) hp

end ClosedSurfaceR4.VelocityFrame

end

end OAI
