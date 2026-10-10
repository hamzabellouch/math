import OAI.Geometry.SurfaceImmersion.Atlas.WeightedRealAlgebra
import OAI.Geometry.Immersion.ClosedSurface.NormalJets

namespace OAI

/-! Explicit polynomial bounds for the Gram determinant, tangential
coefficients and normal projection. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dotBudget (m : ℕ) (C : ℝ) : ℝ := 4*(2^m*C*C)
def quadraticBudget (m : ℕ) (C : ℝ) : ℝ := 1+2*(2^m*dotBudget m C*dotBudget m C)
def inverseGramBudget (m : ℕ) (C K : ℝ) : ℝ :=
  (m.factorial : ℝ)^2*K^(m+1)*(quadraticBudget m C)^m
def liftBudget (m : ℕ) (C K : ℝ) : ℝ := 2^m*quadraticBudget m C*inverseGramBudget m C K
def normalBudget (m : ℕ) (C K : ℝ) : ℝ := C+2*(2^m*liftBudget m C K*C)

lemma dotBudget_nonneg (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ dotBudget m C := by
  unfold dotBudget
  positivity
lemma quadraticBudget_ge_one (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 1 ≤ quadraticBudget m C := by
  have hd := dotBudget_nonneg m hC
  unfold quadraticBudget
  have hh : 0 ≤ 2*(2^m*dotBudget m C*dotBudget m C) := by positivity
  linarith
lemma inverseGramBudget_nonneg (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ inverseGramBudget m C K := by
  have hd := (quadraticBudget_ge_one m hC).trans' zero_le_one
  unfold inverseGramBudget
  positivity
lemma liftBudget_nonneg (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 ≤ liftBudget m C K := by
  have hq := (quadraticBudget_ge_one m hC).trans' zero_le_one
  have hi := inverseGramBudget_nonneg m hC hK
  unfold liftBudget
  positivity

lemma weighted_quadratic_pair {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    {X Y Z W : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bZ : WeightedBound U s m C Z) (bW : WeightedBound U s m C W) :
    WeightedBound U s m (quadraticBudget m C)
      (fun x => (X x ⬝ᵥ Y x)*(Z x ⬝ᵥ W x)-(X x ⬝ᵥ Z x)*(Y x ⬝ᵥ W x)) := by
  have hd := dotBudget_nonneg m hC
  have bd (A B : E → RVec 4) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
      (bA : WeightedBound U s m C A) (bB : WeightedBound U s m C B) :
      WeightedBound U s m (dotBudget m C) (fun x => A x ⬝ᵥ B x) :=
    bA.dot_real hU hs hC hC hA hB bB
  have hleft := (bd X Y hX hY bX bY).mul_real hU hs hd hd
    (contDiffOn_dot_real hX hY) (contDiffOn_dot_real hZ hW) (bd Z W hZ hW bZ bW)
  have hright := (bd X Z hX hZ bX bZ).mul_real hU hs hd hd
    (contDiffOn_dot_real hX hZ) (contDiffOn_dot_real hY hW) (bd Y W hY hW bY bW)
  exact (hleft.sub hU hs
    ((contDiffOn_dot_real hX hY).mul (contDiffOn_dot_real hZ hW))
    ((contDiffOn_dot_real hX hZ).mul (contDiffOn_dot_real hY hW)) hright).mono_const (by
      unfold quadraticBudget
      linarith)

/-- Rational normal projection with an explicit polynomial dependence on
the inverse Gram bound. -/
theorem weighted_realNormalPart {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y W : E → RVec 4}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hW : ContDiffOn ℝ ∞ W U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (bW : WeightedBound U s m C W)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (normalBudget m C K) (fun x => realNormalPart (X x) (Y x) (W x)) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hquad := quadraticBudget_ge_one m hC0
  have hq0 := zero_le_one.trans hquad
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have bG : WeightedBound U s m (quadraticBudget m C)
      (fun x => NormalFrame.gramDet (X x) (Y x)) := by
    convert weighted_quadratic_pair hU hs.le hC0 hX hX hY hY bX bX bY bY using 1
    funext x
    unfold NormalFrame.gramDet
    ring
  have bInv : WeightedBound U s m (inverseGramBudget m C K)
      (fun x => (NormalFrame.gramDet (X x) (Y x))⁻¹) :=
    bG.inv_real hU hs hquad hK hG hne hInv
  have hGI := hG.inv hne
  have bnX := weighted_quadratic_pair hU hs.le hC0 hY hY hX hW bY bY bX bW
  have bnY := weighted_quadratic_pair hU hs.le hC0 hX hX hY hW bX bX bY bW
  have hnX := ((contDiffOn_dot_real hY hY).mul (contDiffOn_dot_real hX hW)).sub
    ((contDiffOn_dot_real hY hX).mul (contDiffOn_dot_real hY hW))
  have hnY := ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hW)).sub
    ((contDiffOn_dot_real hX hY).mul (contDiffOn_dot_real hX hW))
  have bi := inverseGramBudget_nonneg m hC0 hK0
  have blX := bnX.mul_real hU hs.le hq0 bi hnX hGI bInv
  have blY := bnY.mul_real hU hs.le hq0 bi hnY hGI bInv
  have hlX := hnX.mul hGI
  have hlY := hnY.mul hGI
  have hbl := liftBudget_nonneg m hC0 hK0
  have btX := blX.smul_real_pi hU hs hbl hC0 hlX hX bX
  have btY := blY.smul_real_pi hU hs hbl hC0 hlY hY bY
  have hout := (bW.sub hU hs.le hW (hlX.smul hX) btX).sub hU hs.le
    (hW.sub (hlX.smul hX)) (hlY.smul hY) btY
  have hout' := hout.mono_const (show C+2^m*liftBudget m C K*C+2^m*liftBudget m C K*C ≤
      normalBudget m C K from by unfold normalBudget; ring_nf; rfl)
  apply hout'.congr
  intro x hx
  change realNormalPart (X x) (Y x) (W x) =
    W x-(((Y x ⬝ᵥ Y x)*(X x ⬝ᵥ W x)-(Y x ⬝ᵥ X x)*(Y x ⬝ᵥ W x))*
      (NormalFrame.gramDet (X x) (Y x))⁻¹) • X x-
      (((X x ⬝ᵥ X x)*(Y x ⬝ᵥ W x)-(X x ⬝ᵥ Y x)*(X x ⬝ᵥ W x))*
        (NormalFrame.gramDet (X x) (Y x))⁻¹) • Y x
  simp only [realNormalPart,div_eq_mul_inv,dotProduct_comm]

end ClosedSurfaceR4.RealModes

end

end OAI
