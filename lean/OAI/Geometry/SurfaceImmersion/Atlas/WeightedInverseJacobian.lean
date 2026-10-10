import OAI.Geometry.SurfaceImmersion.Geometry.PlaneAdjugate
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedReciprocal
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! Explicit polynomial bounds for the inverse Jacobian field in dimension two. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def inverseJacobianField (A : Base → Base →L[ℝ] Base) (x : Base) : Base →L[ℝ] Base :=
  (coordDet (A x))⁻¹ • planeAdjugate (A x)

lemma contDiffOn_coordDet {U : Set Base} {A : Base → Base →L[ℝ] Base}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun x => coordDet (A x)) U := by
  have hx : ContDiffOn ℝ ∞ (fun x => A x dx) U := hA.clm_apply contDiffOn_const
  have hy : ContDiffOn ℝ ∞ (fun x => A x dy) U := hA.clm_apply contDiffOn_const
  exact (hx.fst.mul hy.snd).sub (hx.snd.mul hy.fst)

lemma contDiffOn_inverseJacobianField {U : Set Base} {A : Base → Base →L[ℝ] Base}
    (hA : ContDiffOn ℝ ∞ A U) (hne : ∀ x ∈ U, coordDet (A x) ≠ 0) :
    ContDiffOn ℝ ∞ (inverseJacobianField A) U :=
  ((contDiffOn_coordDet hA).inv hne).smul
    (planeAdjugateOperator.contDiff.comp_contDiffOn hA)

lemma weighted_coordDet {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → Base →L[ℝ] Base} (hA : ContDiffOn ℝ ∞ A U)
    {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hb : WeightedBound U s m C A) :
    WeightedBound U s m (2^(m+1)*C^2) (fun x => coordDet (A x)) := by
  have he (v : Base) (hv : ‖v‖ ≤ 1) (π : Base →L[ℝ] ℝ) (hπ : ‖π‖ ≤ 1) :
      WeightedBound U s m C (fun x => π (A x v)) := by
    have hh := (hb.clm_apply_const hU hs hA v).linear hU hs
      (hA.clm_apply contDiffOn_const) π
    apply hh.mono_const
    calc
      ‖π‖*(‖v‖*C) ≤ 1*(1*C) := by gcongr
      _ = C := by ring
  have hdx : ‖dx‖ ≤ (1 : ℝ) := by simp [dx]
  have hdy : ‖dy‖ ≤ (1 : ℝ) := by simp [dy]
  have ha := he dx hdx (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ..)
  have hb' := he dy hdy (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ..)
  have hc := he dx hdx (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ..)
  have hd := he dy hdy (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ..)
  have hx : ContDiffOn ℝ ∞ (fun x => A x dx) U := hA.clm_apply contDiffOn_const
  have hy : ContDiffOn ℝ ∞ (fun x => A x dy) U := hA.clm_apply contDiffOn_const
  have had := ha.mul_real hU hs hC hC hx.fst hy.snd hd
  have hcb := hc.mul_real hU hs hC hC hx.snd hy.fst hb'
  have hh := had.sub hU hs (hx.fst.mul hy.snd) (hx.snd.mul hy.fst) hcb
  convert hh using 1
  · rw [pow_succ]
    ring
  · rfl

def inverseJacobianBudget (m : ℕ) (C K : ℝ) : ℝ :=
  2^m*((m.factorial : ℝ)^2*K^(m+1)*(1+2^(m+1)*C^2)^m)*(2*C)

theorem weighted_inverseJacobianField {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → Base →L[ℝ] Base} (hA : ContDiffOn ℝ ∞ A U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hb : WeightedBound U s m C A)
    (hne : ∀ x ∈ U, coordDet (A x) ≠ 0)
    (hinv : ∀ x ∈ U, ‖(coordDet (A x))⁻¹‖ ≤ K) :
    WeightedBound U s m (inverseJacobianBudget m C K) (inverseJacobianField A) := by
  have hC0 := zero_le_one.trans hC
  have hd := weighted_coordDet hU hA hs.le hC0 hb
  have hD : 0 ≤ 2^(m+1)*C^2 := by positivity
  have hd' := hd.mono_const (le_add_of_nonneg_left zero_le_one)
  have hi := hd'.inv_real hU hs (by linarith : 1 ≤ 1+2^(m+1)*C^2) hK
    (contDiffOn_coordDet hA) hne hinv
  have ha := (hb.linear hU hs.le hA planeAdjugateOperator).mono_const
    (mul_le_mul_of_nonneg_right planeAdjugateOperator_norm_le hC0)
  exact hi.smul_real hU hs.le (by positivity) (by positivity)
    ((contDiffOn_coordDet hA).inv hne) (planeAdjugateOperator.contDiff.comp_contDiffOn hA) ha

lemma inverseJacobianBudget_polynomial (m : ℕ) (C K : ℝ → ℝ)
    (hC : HasPolynomialBound C) (hK : HasPolynomialBound K) :
    HasPolynomialBound (fun x => inverseJacobianBudget m (C x) (K x)) := by
  unfold inverseJacobianBudget
  repeat first
    | exact hC
    | exact hK
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

end ClosedSurfaceR4.RealModes

end

end OAI
