import OAI.Geometry.PolarProducts.SmoothFlow

namespace OAI

universe u17 u18 u19 u20 u21 u22

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

open Set Filter Function
open scoped Topology ContDiff

namespace TensorCalculus

variable {E : Type u17} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

abbrev TwoTensor (E : Type u18) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

def evalTensor (a b : E) : TwoTensor E →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ b).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)

@[simp] theorem evalTensor_apply (a b : E) (B : TwoTensor E) :
    evalTensor a b B = B a b := rfl

theorem fderiv_evalTensor {D : Type u19} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → TwoTensor E} {x : D} (hB : DifferentiableAt ℝ B x)
    (d : D) (a b : E) : fderiv ℝ (fun y => B y a b) x d = fderiv ℝ B x d a b := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const a))
    (differentiableAt_const b)]
  rw [fderiv_clm_apply hB (differentiableAt_const a)]
  simp

theorem fderiv_skew {B : E → TwoTensor E} (hB : Differentiable ℝ B)
    (hsk : ∀ x a b, B x a b = -B x b a) (x d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) = fun y => -B y b a := funext (fun y => hsk y a b)
  have he' := congrArg (fun f : E → ℝ => fderiv ℝ f x d) he
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor (hB x), neg_apply] using he'

theorem derivative_kernel {B : E → TwoTensor E} {V : E → E}
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V)
    (hker : ∀ x, B x (V x) = 0) (x a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    (hB x).hasFDerivAt.clm_apply (hV x).hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hker)
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he

theorem invariant_of_closed_kernel {B : E → TwoTensor E} {V : E → E}
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V)
    (hsk : ∀ x a b, B x a b = -B x b a)
    (hclosed : ∀ x a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ x, B x (V x) = 0) (x a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel hB hV hker x a b
  have h2 := derivative_kernel hB hV hker x b a
  have h3 := hclosed x (V x) a b
  have h4 := fderiv_skew hB hsk x a b (V x)
  have h5 := hsk x a (fderiv ℝ V x b)
  linarith

theorem fderiv_skew_at {B : E → TwoTensor E} {x : E} (hB : DifferentiableAt ℝ B x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a) (d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) =ᶠ[𝓝 x] (fun y => -B y b a) :=
    hsk.mono (fun y hy => hy a b)
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L d) he.fderiv_eq
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor hB, neg_apply] using he'

theorem derivative_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    hB.hasFDerivAt.clm_apply hV.hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq hker
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he

theorem invariant_of_closed_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a)
    (hclosed : ∀ a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel_at hB hV hker a b
  have h2 := derivative_kernel_at hB hV hker b a
  have h3 := hclosed (V x) a b
  have h4 := fderiv_skew_at hB hsk a b (V x)
  have h5 := (hsk.self_of_nhds) a (fderiv ℝ V x b)
  linarith

def alt : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ) -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap

@[simp] theorem alt_apply (B : TwoTensor E) (a b : E) :
    alt B a b = B a b - B b a := rfl

def exteriorD (γ : E → E →L[ℝ] ℝ) (x : E) : TwoTensor E :=
  alt (fderiv ℝ γ x)

@[simp] theorem exteriorD_apply (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = fderiv ℝ γ x a b - fderiv ℝ γ x b a := rfl

theorem exteriorD_skew (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = -exteriorD γ x b a := by
  simp only [exteriorD_apply]; ring

theorem fderiv_exteriorD {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : DifferentiableAt ℝ (fderiv ℝ γ) x) (d a b : E) :
    fderiv ℝ (exteriorD γ) x d a b =
      fderiv ℝ (fderiv ℝ γ) x d a b - fderiv ℝ (fderiv ℝ γ) x d b a := by
  change fderiv ℝ (alt ∘ fderiv ℝ γ) x d a b = _
  rw [fderiv_comp x (ContinuousLinearMap.differentiableAt (alt (E := E))) hγ]
  simp

theorem contDiff_exteriorD {γ : E → E →L[ℝ] ℝ}
    (hγ : ContDiff ℝ ∞ γ) : ContDiff ℝ ∞ (exteriorD γ) := by
  change ContDiff ℝ ∞ ((alt (E := E)) ∘ fderiv ℝ γ)
  exact (alt (E := E)).contDiff.comp (hγ.fderiv_right (m := ∞) (by simp))

theorem exteriorD_closed {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : ContDiffAt ℝ ∞ γ x) (a b c : E) :
    fderiv ℝ (exteriorD γ) x a b c + fderiv ℝ (exteriorD γ) x b c a +
      fderiv ℝ (exteriorD γ) x c a b = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ γ) x :=
    (hγ.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiableAt (by simp)
  have hs := hγ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [fderiv_exteriorD hd]
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L c) (hs.eq a b)
  have h2 := congrArg (fun L : E →L[ℝ] ℝ => L a) (hs.eq b c)
  have h3 := congrArg (fun L : E →L[ℝ] ℝ => L b) (hs.eq c a)
  linarith

end
end TensorCalculus

namespace TensorCalculus

open Set Filter Function
open scoped Topology ContDiff

variable {E : Type u20} {F : Type u21} {D : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable section

def pullLinear (L : F →L[ℝ] E) (B : TwoTensor E) : TwoTensor F :=
  B.bilinearComp L L

@[simp] theorem pullLinear_apply (L : F →L[ℝ] E) (B : TwoTensor E) (a b : F) :
    pullLinear L B a b = B (L a) (L b) := rfl

theorem contDiffAt_pullLinear (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun x => pullLinear L (B x)) z := by
  let P : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip L
  change ContDiffAt ℝ ∞ (fun x => P.comp ((B x).comp L)) z
  exact contDiffAt_const.clm_comp (hB.clm_comp contDiffAt_const)

theorem fderiv_pullLinear_eval (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : DifferentiableAt ℝ B z)
    (hP : DifferentiableAt ℝ (fun x => pullLinear L (B x)) z) (d : D) (a b : F) :
    fderiv ℝ (fun x => pullLinear L (B x)) z d a b =
      fderiv ℝ B z d (L a) (L b) := by
  rw [← fderiv_evalTensor hP, ← fderiv_evalTensor hB]
  rfl

theorem pullLinear_closed (L : F →L[ℝ] E) {B : E → TwoTensor E} {z : F}
    (hB : ContDiffAt ℝ ∞ B (L z))
    (hclosed : ∀ a b c, fderiv ℝ B (L z) a b c +
      fderiv ℝ B (L z) b c a + fderiv ℝ B (L z) c a b = 0) (a b c : F) :
    fderiv ℝ (fun x => pullLinear L (B (L x))) z a b c +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z b c a +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z c a b = 0 := by
  have hs : ContDiffAt ℝ ∞ (fun x => B (L x)) z := hB.comp z L.contDiff.contDiffAt
  have ht := contDiffAt_pullLinear L hs
  have he (d u v : F) :
      fderiv ℝ (fun x => pullLinear L (B (L x))) z d u v =
        fderiv ℝ B (L z) (L d) (L u) (L v) := by
    rw [fderiv_pullLinear_eval L (hs.differentiableAt (by simp))
      (ht.differentiableAt (by simp))]
    rw [fderiv_fun_comp z (hB.differentiableAt (by simp)) L.differentiableAt]
    simp
  simp only [he]
  exact hclosed (L a) (L b) (L c)

end
end TensorCalculus

end LowerBoundInline

end OAI
