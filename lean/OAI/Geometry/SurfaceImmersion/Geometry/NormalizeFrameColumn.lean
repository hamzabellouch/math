import OAI.Geometry.SurfaceImmersion.Whitney.ShiftedRotationFrame

namespace OAI

/-! Positive normalization of the first column of a smooth rank-two frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def scaleFirstInput (r : ℝ) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj 0).smulRight (![r,0] : Base)+
    (ContinuousLinearMap.proj 1).smulRight (![0,1] : Base)

lemma scaleFirstInput_apply (r : ℝ) (v : Base) :
    scaleFirstInput r v = ![r*v 0,v 1] := by
  ext i
  fin_cases i <;> simp [scaleFirstInput,mul_comm]

lemma scaleFirstInput_injective {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (scaleFirstInput r) := by
  intro u v he
  rw [scaleFirstInput_apply,scaleFirstInput_apply] at he
  have h0 : u 0 = v 0 := mul_left_cancel₀ hr (congrFun he 0)
  have h1 : u 1 = v 1 := congrFun he 1
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma scaleFirstInput_smooth : ContDiff ℝ ∞ scaleFirstInput := by
  have hV : ContDiff ℝ ∞ (fun r : ℝ => (![r,0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
  exact (contDiff_const.smulRight hV).add contDiff_const

def firstColumnLength (L : Base →L[ℝ] FrameTarget) : ℝ :=
  Real.sqrt ((L (![1,0] : Base) 0)^2+(L (![1,0] : Base) 1)^2+(L (![1,0] : Base) 2)^2)

def normalizeFrameColumn (L : Base →L[ℝ] FrameTarget) : Base →L[ℝ] FrameTarget :=
  L.comp (scaleFirstInput (firstColumnLength L)⁻¹)

lemma firstColumnLength_pos {L : Base →L[ℝ] FrameTarget} (hL : Function.Injective L) :
    0 < firstColumnLength L := by
  apply Real.sqrt_pos.mpr
  by_contra hn
  have hs : (L (![1,0] : Base) 0)^2+(L (![1,0] : Base) 1)^2+(L (![1,0] : Base) 2)^2 ≤ 0 :=
    le_of_not_gt hn
  have h0 : L (![1,0] : Base) 0 = 0 := by nlinarith [sq_nonneg (L ![1,0] 0),sq_nonneg (L ![1,0] 1),sq_nonneg (L ![1,0] 2)]
  have h1 : L (![1,0] : Base) 1 = 0 := by nlinarith [sq_nonneg (L ![1,0] 0),sq_nonneg (L ![1,0] 1),sq_nonneg (L ![1,0] 2)]
  have h2 : L (![1,0] : Base) 2 = 0 := by nlinarith [sq_nonneg (L ![1,0] 0),sq_nonneg (L ![1,0] 1),sq_nonneg (L ![1,0] 2)]
  have hz : L (![1,0] : Base) = L 0 := by
    rw [map_zero]
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have he := congrFun (hL hz) 0
  norm_num at he

lemma normalizeFrameColumn_injective {L : Base →L[ℝ] FrameTarget} (hL : Function.Injective L) :
    Function.Injective (normalizeFrameColumn L) :=
  hL.comp (scaleFirstInput_injective (inv_ne_zero (firstColumnLength_pos hL).ne'))

lemma firstColumnLength_smooth {A : Base → Base →L[ℝ] FrameTarget} (hA : ContDiff ℝ ∞ A)
    (hI : ∀ x, Function.Injective (A x)) : ContDiff ℝ ∞ (fun x => firstColumnLength (A x)) := by
  have hv := hA.clm_apply (contDiff_const (c := (![1,0] : Base)))
  have h0 : ContDiff ℝ ∞ (fun x => (A x) (![1,0] : Base) 0) := (contDiff_apply ℝ ℝ 0).comp hv
  have h1 : ContDiff ℝ ∞ (fun x => (A x) (![1,0] : Base) 1) := (contDiff_apply ℝ ℝ 1).comp hv
  have h2 : ContDiff ℝ ∞ (fun x => (A x) (![1,0] : Base) 2) := (contDiff_apply ℝ ℝ 2).comp hv
  apply ((h0.pow 2).add (h1.pow 2) |>.add (h2.pow 2)).sqrt
  intro x
  exact (Real.sqrt_pos.mp (firstColumnLength_pos (hI x))).ne'

lemma normalizeFrameColumn_smooth {A : Base → Base →L[ℝ] FrameTarget} (hA : ContDiff ℝ ∞ A)
    (hI : ∀ x, Function.Injective (A x)) : ContDiff ℝ ∞ (fun x => normalizeFrameColumn (A x)) :=
  hA.clm_comp (scaleFirstInput_smooth.comp
    ((firstColumnLength_smooth hA hI).inv (fun x => (firstColumnLength_pos (hI x)).ne')))

lemma firstColumnLength_axisNormalFrame (r y z : ℝ) (hr : 0 ≤ r) :
    firstColumnLength (axisNormalFrame r y z) = r := by
  simp [firstColumnLength,axisNormalFrame,Real.sqrt_sq hr]

lemma normalizeFrameColumn_axisNormalFrame (r y z : ℝ) (hr : 0 < r) :
    normalizeFrameColumn (axisNormalFrame r y z) = axisNormalFrame 1 y z := by
  rw [normalizeFrameColumn,firstColumnLength_axisNormalFrame r y z hr.le]
  ext v i
  fin_cases i <;> simp [ContinuousLinearMap.comp_apply,scaleFirstInput_apply,axisNormalFrame,
    hr.ne',mul_comm,mul_left_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
