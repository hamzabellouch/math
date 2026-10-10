import OAI.Geometry.PolarProducts.MoserFlow

namespace OAI

universe u27 u28 u29

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped Topology ContDiff

variable {E : Type u27} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def dcOp (J : E →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 4 : ℝ) • (ContinuousLinearMap.compL ℝ E E ℝ).flip J

def dc (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  dcOp J (fderiv ℝ φ x)

def ddc (J : E →L[ℝ] E) (φ : E → ℝ) : E → TwoTensor E := exteriorD (dc J φ)

@[simp] theorem dcOp_apply (J : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (a : E) :
    dcOp J L a = -(L (J a)) / 4 := by
  simp only [dcOp, smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

@[simp] theorem dc_apply (J : E →L[ℝ] E) (φ : E → ℝ) (x a : E) :
    dc J φ x a = -(fderiv ℝ φ x (J a)) / 4 := dcOp_apply J _ a

theorem contDiffAt_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (dc J φ) x := by
  change ContDiffAt ℝ ∞ (dcOp J ∘ fderiv ℝ φ) x
  exact (dcOp J).contDiff.contDiffAt.comp x (hφ.fderiv_right (m := ∞) (by simp))

theorem contDiff_dc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (dc J φ) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => contDiffAt_dc J (hφ.contDiffAt (x := x))

theorem fderiv_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a b : E) :
    fderiv ℝ (dc J φ) x a b = -(fderiv ℝ (fderiv ℝ φ) x a (J b)) / 4 := by
  change fderiv ℝ (dcOp J ∘ fderiv ℝ φ) x a b = _
  rw [fderiv_comp x (dcOp J).differentiableAt hφ]
  simp

theorem ddc_apply (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a b : E) :
    ddc J φ x a b =
      (fderiv ℝ (fderiv ℝ φ) x b (J a) - fderiv ℝ (fderiv ℝ φ) x a (J b)) / 4 := by
  simp only [ddc, exteriorD_apply, fderiv_dc J hφ]
  ring

theorem ddc_skew (J : E →L[ℝ] E) (φ : E → ℝ) (x a b : E) :
    ddc J φ x a b = -ddc J φ x b a := exteriorD_skew _ _ _ _

theorem contDiffAt_ddc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (ddc J φ) x := by
  change ContDiffAt ℝ ∞ (alt ∘ fderiv ℝ (dc J φ)) x
  exact (alt (E := E)).contDiff.contDiffAt.comp x
    ((contDiffAt_dc J hφ).fderiv_right (m := ∞) (by simp))

theorem contDiff_ddc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (ddc J φ) :=
  contDiff_exteriorD (contDiff_dc J hφ)

theorem ddc_closed (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (a b c : E) :
    fderiv ℝ (ddc J φ) x a b c + fderiv ℝ (ddc J φ) x b c a +
      fderiv ℝ (ddc J φ) x c a b = 0 := exteriorD_closed (contDiffAt_dc J hφ) a b c

theorem ddc_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a : E) :
    ddc J φ x a (J a) =
      (fderiv ℝ (fderiv ℝ φ) x a a + fderiv ℝ (fderiv ℝ φ) x (J a) (J a)) / 4 := by
  rw [ddc_apply J hφ, hJ]
  simp only [map_neg]
  ring

def IsPSHAt (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : Prop :=
  ContDiffAt ℝ ∞ φ x ∧ ∀ a, 0 ≤ ddc J φ x a (J a)

theorem dc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : dc J φ x = dc J ψ x := by
  rw [dc, dc, h.fderiv_eq]

theorem ddc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : ddc J φ x = ddc J ψ x := by
  have he : dc J φ =ᶠ[𝓝 x] dc J ψ := h.eventuallyEq_nhds.mono (fun y hy => dc_congr J hy)
  simpa only [ddc, exteriorD] using congrArg alt he.fderiv_eq

theorem dc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    dc J (fun y => φ y + ψ y) x = dc J φ x + dc J ψ x := by
  simp only [dc, fderiv_fun_add hφ hψ, map_add]

theorem ddc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y + ψ y) x = ddc J φ x + ddc J ψ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => φ y + ψ y) =ᶠ[𝓝 x] fun y => dc J φ y + dc J ψ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      (hψ.of_le h1).eventually (by simp)] with y hy hz
    exact dc_add J (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))
  unfold ddc exteriorD
  rw [he.fderiv_eq, fderiv_fun_add
    ((contDiffAt_dc J hφ).differentiableAt (by simp))
    ((contDiffAt_dc J hψ).differentiableAt (by simp)), map_add]

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus
open scoped ContDiff Topology

variable {E : Type u28} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

def standardTensor (J : E →L[ℝ] E) : TwoTensor E := (innerSL ℝ).comp J

@[simp] theorem standardTensor_apply (J : E →L[ℝ] E) (a b : E) :
    standardTensor J a b = inner (𝕜 := ℝ) (J a) b := rfl

theorem dc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    dc J (fun x : E => ‖x‖^2) x = (1 / 2 : ℝ) • standardTensor J x := by
  ext a
  rw [dc_apply, fderiv_norm_sq_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, standardTensor_apply]
  rw [hsk]
  ring

theorem ddc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    ddc J (fun x : E => ‖x‖^2) x = standardTensor J := by
  have he : dc J (fun x : E => ‖x‖^2) = fun x => (1 / 2 : ℝ) • standardTensor J x :=
    funext (dc_norm_sq J hsk)
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [ddc, he, exteriorD_apply]
  have hd : fderiv ℝ (fun x => (1 / 2 : ℝ) • standardTensor J x) x =
      (1 / 2 : ℝ) • standardTensor J := by
    exact ((standardTensor J).hasFDerivAt.const_smul (1 / 2 : ℝ)).fderiv
  rw [hd]
  simp only [smul_apply, smul_eq_mul, standardTensor_apply]
  have hh : inner (𝕜 := ℝ) (J b) a = -inner (𝕜 := ℝ) (J a) b := by
    rw [real_inner_comm, hsk]
  rw [hh]
  ring

theorem standardTensor_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, ‖J a‖ = ‖a‖) (a : E) :
    standardTensor J a (J a) = ‖a‖^2 := by
  rw [standardTensor_apply, real_inner_self_eq_norm_sq, hJ]

theorem isInvertible_of_positive_complex_line [FiniteDimensional ℝ E]
    (B : TwoTensor E) (J : E →L[ℝ] E) (hp : ∀ a : E, a ≠ 0 → 0 < B a (J a)) :
    B.IsInvertible := by
  have hi : Function.Injective B := by
    intro a b hab
    have hz : B (a - b) = 0 := by rw [map_sub, hab, sub_self]
    by_contra hn
    have hpos := hp (a - b) (sub_ne_zero.mpr hn)
    rw [hz, zero_apply] at hpos
    exact (lt_irrefl 0) hpos
  let e := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv
  let L : E →L[ℝ] E := e.symm.toContinuousLinearMap.comp B
  have hL : Function.Injective L := e.symm.injective.comp hi
  have hsL : Function.Surjective L := LinearMap.surjective_of_injective hL
  have hs : Function.Surjective B := by
    intro v
    obtain ⟨x, hx⟩ := hsL (e.symm v)
    refine ⟨x, ?_⟩
    exact e.symm.injective hx
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem isInvertible_ddc_norm_sq_add [FiniteDimensional ℝ E]
    (J : E →L[ℝ] E) (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) {φ : E → ℝ} {x : E} (hφ : IsPSHAt J φ x) :
    (ddc J (fun y => ‖y‖^2 + φ y) x).IsInvertible := by
  apply isInvertible_of_positive_complex_line _ J
  intro a ha
  rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt hφ.1, add_apply, add_apply,
    ddc_norm_sq J hsk, standardTensor_complex_line J hJ]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr ha)) (hφ.2 a)

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u29} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance linearOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance linearOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance linearTwoGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearTwoSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

@[simp] theorem dc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    dc J (fun _ => c) x = 0 := by
  simp [dc]

@[simp] theorem ddc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    ddc J (fun _ => c) x = 0 := by
  simp [ddc, exteriorD, show dc J (fun _ : E => c) = fun _ => 0 by funext y; simp]

theorem dc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    dc J (fun y => c * φ y) x = c • dc J φ x := by
  ext a
  rw [dc_apply, fderiv_const_mul hφ]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring

theorem ddc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => c * φ y) x = c • ddc J φ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => c * φ y) =ᶠ[𝓝 x] fun y => c • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp)] with y hy
    exact dc_const_smul J c (hy.differentiableAt one_ne_zero)
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  have hd : fderiv ℝ (fun y => c • dc J φ y) x = c • fderiv ℝ (dc J φ) x :=
    (((contDiffAt_dc J hφ).differentiableAt (by simp)).hasFDerivAt.const_smul c).fderiv
  rw [hd, map_smul]

theorem ddc_neg (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => -φ y) x = -ddc J φ x := by
  simpa only [neg_one_mul, neg_one_smul] using ddc_const_smul J (-1) hφ

theorem ddc_sub (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y - ψ y) x = ddc J φ x - ddc J ψ x := by
  simp_rw [sub_eq_add_neg]
  rw [ddc_add J hφ hψ.neg, ddc_neg J hψ]

theorem ddc_add_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y + c) x = ddc J φ x := by
  rw [ddc_add J hφ contDiffAt_const, ddc_const, add_zero]

theorem ddc_sub_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y - c) x = ddc J φ x := by
  rw [ddc_sub J hφ contDiffAt_const, ddc_const, sub_zero]

theorem IsPSHAt.add {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => φ y + ψ y) x := by
  refine ⟨hφ.1.add hψ.1, fun a => ?_⟩
  rw [ddc_add J hφ.1 hψ.1, add_apply, add_apply]
  exact add_nonneg (hφ.2 a) (hψ.2 a)

theorem IsPSHAt.const_smul {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) {c : ℝ} (hc : 0 ≤ c) :
    IsPSHAt J (fun y => c * φ y) x := by
  refine ⟨contDiffAt_const.mul hφ.1, fun a => ?_⟩
  rw [ddc_const_smul J c hφ.1]
  simpa only [smul_apply, smul_eq_mul] using mul_nonneg hc (hφ.2 a)

theorem IsPSHAt.sub_const {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (c : ℝ) : IsPSHAt J (fun y => φ y - c) x := by
  refine ⟨hφ.1.sub contDiffAt_const, fun a => ?_⟩
  rw [ddc_sub_const J hφ.1 c]
  exact hφ.2 a

end
end ComplexPotential

end LowerBoundInline

end OAI
