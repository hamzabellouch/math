import OAI.Geometry.SurfaceImmersion.Geometry.RealJetCoefficients

namespace OAI

/-! Polynomial estimates for the three vector columns of reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangentDualBudget (m : ℕ) (C K : ℝ) :=
  2*(2^m*(2^m*dotBudget m C*inverseGramBudget m C K)*C)

def normalDualBudget (m : ℕ) (C K : ℝ) :=
  2^m*((m.factorial : ℝ)^2*K^(m+1)*(1+dotBudget m C)^m)*C

lemma weighted_realTangentDuals {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    {X Y : E → RVec 4} (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (bX : WeightedBound U s m C X) (bY : WeightedBound U s m C Y)
    (hne : ∀ x ∈ U, NormalFrame.gramDet (X x) (Y x) ≠ 0)
    (hInv : ∀ x ∈ U, ‖(NormalFrame.gramDet (X x) (Y x))⁻¹‖ ≤ K) :
    WeightedBound U s m (tangentDualBudget m C K) (fun x => realTangentDualX (X x) (Y x)) ∧
    WeightedBound U s m (tangentDualBudget m C K) (fun x => realTangentDualY (X x) (Y x)) := by
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hdb := dotBudget_nonneg m hC0
  have hib := inverseGramBudget_nonneg m hC0 hK0
  have hG : ContDiffOn ℝ ∞ (fun x => NormalFrame.gramDet (X x) (Y x)) U :=
    ((contDiffOn_dot_real hX hX).mul (contDiffOn_dot_real hY hY)).sub
      ((contDiffOn_dot_real hX hY).pow 2)
  have hGI := hG.inv hne
  have bi := weighted_inverse_gramDet hU hs hC hK hX hY bX bY hne hInv
  have bxx : WeightedBound U s m (dotBudget m C) (fun x => X x ⬝ᵥ X x) :=
    bX.dot_real hU hs.le hC0 hC0 hX hX bX
  have bxy : WeightedBound U s m (dotBudget m C) (fun x => X x ⬝ᵥ Y x) :=
    bX.dot_real hU hs.le hC0 hC0 hX hY bY
  have byy : WeightedBound U s m (dotBudget m C) (fun x => Y x ⬝ᵥ Y x) :=
    bY.dot_real hU hs.le hC0 hC0 hY hY bY
  have hxx := (contDiffOn_dot_real hX hX).mul hGI
  have hxy := (contDiffOn_dot_real hX hY).mul hGI
  have hyy := (contDiffOn_dot_real hY hY).mul hGI
  have cxx := bxx.mul_real hU hs.le hdb hib (contDiffOn_dot_real hX hX) hGI bi
  have cxy := bxy.mul_real hU hs.le hdb hib (contDiffOn_dot_real hX hY) hGI bi
  have cyy := byy.mul_real hU hs.le hdb hib (contDiffOn_dot_real hY hY) hGI bi
  have hc : 0 ≤ 2^m*dotBudget m C*inverseGramBudget m C K := by positivity
  have vxx := cxx.smul_real_pi hU hs hc hC0 hxx hY bY
  have vyx := cyy.smul_real_pi hU hs hc hC0 hyy hX bX
  have vxy := cxy.smul_real_pi hU hs hc hC0 hxy hX bX
  have vyy := cxy.smul_real_pi hU hs hc hC0 hxy hY bY
  constructor
  · have hh := vyx.sub hU hs.le (hyy.smul hX) (hxy.smul hY) vyy
    have hh' : WeightedBound U s m (tangentDualBudget m C K)
        (fun x => ((Y x ⬝ᵥ Y x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • X x-
          ((X x ⬝ᵥ Y x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • Y x) := by
      convert hh using 1
      unfold tangentDualBudget
      ring
    apply hh'.congr
    intro x hx
    simp [realTangentDualX,div_eq_mul_inv,sub_eq_add_neg]
  · have hh := vxx.sub hU hs.le (hxx.smul hY) (hxy.smul hX) vxy
    have hh' : WeightedBound U s m (tangentDualBudget m C K)
        (fun x => ((X x ⬝ᵥ X x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • Y x-
          ((X x ⬝ᵥ Y x)*(NormalFrame.gramDet (X x) (Y x))⁻¹) • X x) := by
      convert hh using 1
      unfold tangentDualBudget
      ring
    apply hh'.congr
    intro x hx
    simp [realTangentDualY,div_eq_mul_inv,sub_eq_add_neg,add_comm]

lemma weighted_vector_over_norm_sq {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C) (hK : 1 ≤ K)
    {V : E → RVec 4} (hV : ContDiffOn ℝ ∞ V U) (bV : WeightedBound U s m C V)
    (hpos : ∀ x ∈ U, 0 < V x ⬝ᵥ V x) (hi : ∀ x ∈ U, (V x ⬝ᵥ V x)⁻¹ ≤ K) :
    WeightedBound U s m (normalDualBudget m C K) (fun x => (V x ⬝ᵥ V x)⁻¹ • V x) := by
  have hdot := contDiffOn_dot_real hV hV
  have hd := dotBudget_nonneg m hC
  have bdot : WeightedBound U s m (1+dotBudget m C) (fun x => V x ⬝ᵥ V x) :=
    (bV.dot_real hU hs.le hC hC hV hV bV).mono_const (by change dotBudget m C ≤ _; linarith)
  have hinv : ∀ x ∈ U, ‖(V x ⬝ᵥ V x)⁻¹‖ ≤ K := by
    intro x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hpos x hx).le)] using hi x hx
  have bi := bdot.inv_real hU hs (by linarith : 1 ≤ 1+dotBudget m C) hK hdot
    (fun x hx => (hpos x hx).ne') hinv
  exact bi.smul_real_pi hU hs (by positivity) hC (hdot.inv (fun x hx => (hpos x hx).ne')) hV bV

end ClosedSurfaceR4.RealModes

end

end OAI
