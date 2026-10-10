import OAI.Geometry.PolarProducts.MoserField

namespace OAI

universe u25 u26

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

namespace SmoothODE

variable {E : Type u25} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

def fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) : E ≃ₜ E where
  toFun x := (f (t, x)).2
  invFun y := (f.symm (t + T, y)).2
  left_inv x := by
    have he : (t + T, (f (t, x)).2) = f (t, x) := by
      ext
      · exact (hTime (t, x)).symm
      · rfl
    change (f.symm (t + T, (f (t, x)).2)).2 = x
    rw [he, f.symm_apply_apply]
  right_inv y := by
    have he : (f.symm (t + T, y)).1 = t := by
      have h := hTime (f.symm (t + T, y))
      rw [f.apply_symm_apply] at h
      dsimp at h
      linarith
    have he' : (t, (f.symm (t + T, y)).2) = f.symm (t + T, y) := by
      ext
      · exact he.symm
      · rfl
    change (f (t, (f.symm (t + T, y)).2)).2 = y
    rw [he', f.apply_symm_apply]
  continuous_toFun := continuous_snd.comp (f.continuous.comp (continuous_const.prodMk continuous_id))
  continuous_invFun := continuous_snd.comp
    (f.symm.continuous.comp (continuous_const.prodMk continuous_id))

omit [NormedSpace ℝ E] in
@[simp] theorem fiberHomeomorph_apply (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) (x : E) :
    fiberHomeomorph f T hTime t x = (f (t, x)).2 := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem fiberHomeomorph_symm_apply (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) (x : E) :
    (fiberHomeomorph f T hTime t).symm x = (f.symm (t + T, x)).2 := rfl

theorem contDiff_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) :
    ContDiff ℝ ∞ (fiberHomeomorph f T hTime t : E → E) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).snd

theorem contDiff_fiberHomeomorph_symm (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E))) :
    ContDiff ℝ ∞ ((fiberHomeomorph f T hTime t).symm : E → E) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).snd

theorem fderiv_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) (x a : E) :
    fderiv ℝ (f : (ℝ × E) → (ℝ × E)) (t, x) (0, a) =
      (0, fderiv ℝ (fiberHomeomorph f T hTime t : E → E) x a) := by
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    have hh := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
    have he : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.inr ℝ ℝ E := by
      ext y <;> rfl
    rw [he] at hh
    exact hh
  have hd := (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp x hi
  change HasFDerivAt (fun y : E => f (t, y)) _ x at hd
  have he : (fun y : E => f (t, y)) =
      fun y => (t + T, fiberHomeomorph f T hTime t y) := by
    funext y
    exact Prod.ext (hTime (t, y)) rfl
  have hd' := (hasFDerivAt_const (𝕜 := ℝ) (t + T) x).prodMk
    ((contDiff_fiberHomeomorph f T hTime t hf).differentiable (by simp) x).hasFDerivAt
  have hu := congrArg (fun L : E →L[ℝ] (ℝ × E) => L a)
    ((he ▸ hd).unique hd')
  simpa using hu

omit [NormedSpace ℝ E] in

theorem fiberHomeomorph_mapsTo (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) {U : Set E}
    (hOut : ∀ z, z.2 ∉ U → (f z).2 = z.2) :
    ∀ x, fiberHomeomorph f T hTime t x ∈ U ↔ x ∈ U := by
  intro x
  constructor
  · intro hx
    by_contra hc
    rw [fiberHomeomorph_apply, hOut (t, x) hc] at hx
    exact hc hx
  · intro hx
    by_contra hc
    have he : fiberHomeomorph f T hTime t (fiberHomeomorph f T hTime t x) =
        fiberHomeomorph f T hTime t x := hOut _ hc
    have hu := (fiberHomeomorph f T hTime t).injective he
    exact hc (hu.symm ▸ hx)

end
end SmoothODE

namespace Moser

open Set Filter Function TensorCalculus SmoothODE
open scoped Topology ContDiff NNReal

variable {E : Type u26} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem compactlySupported_deformation {U : Set E} (hU : IsOpen U)
    {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    (hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x)
    (hsk : ∀ x ∈ U, ∀ a b, W x a b = -W x b a)
    (hclosed : ∀ x ∈ U, ∀ a b c,
      fderiv ℝ W x a b c + fderiv ℝ W x b c a + fderiv ℝ W x c a b = 0)
    (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ) (hs : tsupport γ ⊆ U)
    (hi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        (W (F x) + exteriorD γ (F x)) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = W x a b := by
  let A := spatialTensor W γ timeCutoff
  let Y := spatialField A γ (deriv timeCutoff)
  let V : (ℝ × E) → (ℝ × E) := fun z => (1, Y z)
  let B := spaceTimeTensor W γ timeCutoff
  have hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z := by
    intro z hz
    exact contDiffAt_spatialTensor (hW z.2 hz) hγ timeCutoff_smooth
  have hAi : ∀ z, z.2 ∈ U → (A z).IsInvertible := by
    intro z hz
    exact hi z.2 hz _ (timeCutoff_mem z.1)
  have hY : ContDiff ℝ ∞ Y :=
    contDiff_spatialField hA hAi hγ timeCutoff_deriv_smooth hs
  have hV : ContDiff ℝ ∞ V := contDiff_const.prodMk hY
  obtain ⟨K, hK⟩ := exists_lipschitz_spaceTimeField hA hAi hγ
    timeCutoff_deriv_smooth hs hcγ timeCutoff_deriv_hasCompactSupport
  have hOut : ∀ z, z.2 ∉ U → (V z).2 = 0 := by
    intro z hz
    exact spatialField_eq_zero_of_oneForm_eq_zero A γ (deriv timeCutoff) z
      (image_eq_zero_of_notMem_tsupport (fun hc => hz (hs hc)))
  have hB : ∀ z, z.2 ∈ U → DifferentiableAt ℝ B z := by
    intro z hz
    exact (contDiffAt_spaceTimeTensor (hW z.2 hz) hγ timeCutoff_smooth).differentiableAt
      (by simp)
  have hIv : ∀ z, z.2 ∈ U → ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0 := by
    intro z hz a b
    have hn : ∀ᶠ y in 𝓝 z, y.2 ∈ U := continuous_snd.continuousAt (hU.mem_nhds hz)
    apply invariant_of_closed_kernel_at (hB z hz) (hV.differentiable (by simp) z)
      (hn.mono (fun y hy => spaceTimeTensor_skew W γ timeCutoff (hsk y.2 hy)))
      (spaceTimeTensor_closed (hW z.2 hz) hγ timeCutoff_smooth (hclosed z.2 hz))
      (hn.mono (fun y hy => spaceTimeTensor_kernel (hγ.differentiable (by simp) y.2)
        (timeCutoff_smooth.differentiable (by simp) y.1) (hAi y hy) (hsk y.2 hy)))
  obtain ⟨f, hf, hfi, htime, hout, htrans⟩ :=
    exists_spaceTime_transport hK hV (fun _ => rfl) hOut hB hIv 1
  let F := fiberHomeomorph f 1 htime 0
  have hF : ContDiff ℝ ∞ (F : E → E) := contDiff_fiberHomeomorph f 1 htime 0 hf
  have hFi : ContDiff ℝ ∞ (F.symm : E → E) := contDiff_fiberHomeomorph_symm f 1 htime 0 hfi
  refine ⟨F, hF, hFi, ?_, fiberHomeomorph_mapsTo f 1 htime 0 hout, ?_⟩
  · intro x hx
    exact hout (0, x) hx
  · intro x hx a b
    have hh := (htrans (0, x) hx).2 (0, a) (0, b)
    rw [fderiv_fiberHomeomorph f 1 htime 0 hf x a,
      fderiv_fiberHomeomorph f 1 htime 0 hf x b] at hh
    have he : f (0, x) = (1, F x) := by
      apply Prod.ext
      · simpa using htime (0, x)
      · rfl
    rw [he] at hh
    have hb (z : ℝ × E) (a b : E) : B z (0, a) (0, b) = A z a b := by
      dsimp only [B, A]
      rw [spaceTimeTensor_apply (hγ.differentiable (by simp) z.2)
        (timeCutoff_smooth.differentiable (by simp) z.1)]
      simp
    rw [hb, hb] at hh
    simpa only [A, spatialTensor, timeCutoff_zero, timeCutoff_one,
      one_smul, zero_smul, add_zero, add_apply, smul_apply, smul_eq_mul, zero_mul] using hh

end
end Moser

end LowerBoundInline

end OAI
