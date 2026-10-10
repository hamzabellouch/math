import OAI.Geometry.SurfaceImmersion.Correction.PolynomialNormalBounds

namespace OAI

/-! Polynomial bounds for the tangential reconstruction coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realConnectionX (X Y W : RVec 4) : ℝ :=
  ((Y ⬝ᵥ Y)*(X ⬝ᵥ W)-(X ⬝ᵥ Y)*(Y ⬝ᵥ W))/NormalFrame.gramDet X Y

def realConnectionY (X Y W : RVec 4) : ℝ :=
  ((X ⬝ᵥ X)*(Y ⬝ᵥ W)-(X ⬝ᵥ Y)*(X ⬝ᵥ W))/NormalFrame.gramDet X Y

lemma weighted_inverse_gramDet {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y : E → RVec 4} (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (inverseGramBudget m C K)
      (fun x => (NormalFrame.gramDet (X x) (Y x))⁻¹) := by
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have bG : WeightedBound U s m (quadraticBudget m C)
      (fun x => NormalFrame.gramDet (X x) (Y x)) := by
    convert weighted_quadratic_pair hU hs.le (zero_le_one.trans hC) hX hX hY hY bX bX bY bY using 1
    funext x
    unfold NormalFrame.gramDet
    ring
  exact bG.inv_real hU hs (quadraticBudget_ge_one m (zero_le_one.trans hC)) hK hG hne hInv

theorem weighted_realConnections {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y W : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hW : ContDiffOn ℝ ∞ W U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bW : WeightedBound U s m C W)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (liftBudget m C K) (fun x => realConnectionX (X x) (Y x) (W x)) ∧
    WeightedBound U s m (liftBudget m C K) (fun x => realConnectionY (X x) (Y x) (W x)) := by
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hq := zero_le_one.trans (quadraticBudget_ge_one m hC0)
  have hi := inverseGramBudget_nonneg m hC0 hK0
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have hGI := hG.inv hne
  have bInv := weighted_inverse_gramDet hU hs hC hK hX hY bX bY hne hInv
  have hnX := ((contDiffOn_dot_real hY hY).mul (contDiffOn_dot_real hX hW)).sub
    ((contDiffOn_dot_real hY hX).mul (contDiffOn_dot_real hY hW))
  have hnY := ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hW)).sub
    ((contDiffOn_dot_real hX hY).mul (contDiffOn_dot_real hX hW))
  have bnx := weighted_quadratic_pair hU hs.le hC0 hY hY hX hW bY bY bX bW
  have bny := weighted_quadratic_pair hU hs.le hC0 hX hX hY hW bX bX bY bW
  constructor
  · apply (bnx.mul_real hU hs.le hq hi hnX hGI bInv).congr
    intro x hx
    change realConnectionX (X x) (Y x) (W x) = _
    simp only [realConnectionX,div_eq_mul_inv,dotProduct_comm]
    rfl
  · apply (bny.mul_real hU hs.le hq hi hnY hGI bInv).congr
    intro x hx
    change realConnectionY (X x) (Y x) (W x) = _
    rfl

end ClosedSurfaceR4.RealModes

end

end OAI
