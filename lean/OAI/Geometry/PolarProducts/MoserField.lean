import OAI.Geometry.PolarProducts.TensorCalculus

namespace OAI

universe u23 u24

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

namespace Moser

variable {E : Type u23} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

def spatialField (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) : E :=
  -(ρ z.1) • (A z).inverse (γ z.2)

omit [CompleteSpace E] in
theorem spatialField_eq_zero_of_oneForm_eq_zero
    (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) (hz : γ z.2 = 0) :
    spatialField A γ ρ z = 0 := by simp [spatialField, hz]

omit [CompleteSpace E] in
theorem contract_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) (hA : (A z).IsInvertible) :
    A z (spatialField A γ ρ z) = -(ρ z.1) • γ z.2 := by
  simp only [spatialField, map_smul, hA.self_apply_inverse]

omit [CompleteSpace E] in

theorem oneForm_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E)
    (hA : (A z).IsInvertible) (hsk : ∀ a b, A z a b = -A z b a) :
    γ z.2 (spatialField A γ ρ z) = 0 := by
  let v := (A z).inverse (γ z.2)
  have he : A z v = γ z.2 := hA.self_apply_inverse _
  have hh := hsk v v
  have hz : A z v v = 0 := by linarith
  have hγv : γ z.2 v = 0 := by rw [← he]; exact hz
  simpa [spatialField, v, map_smul, smul_eq_mul] using
    congrArg (fun t : ℝ => -(ρ z.1) * t) hγv

theorem contDiff_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ} {U : Set E}
    (hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z)
    (hi : ∀ z, z.2 ∈ U → (A z).IsInvertible)
    (hγ : ContDiff ℝ ∞ γ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport γ ⊆ U) :
    ContDiff ℝ ∞ (spatialField A γ ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ U
  · have hv : ContDiffAt ℝ ∞ (fun x => (A x).inverse) z :=
      (hi z hz).contDiffAt_map_inverse.comp z (hA z hz)
    exact ((hρ.contDiffAt.comp z contDiffAt_fst).neg).smul
      (hv.clm_apply (hγ.contDiffAt.comp z contDiffAt_snd))
  · have ht : z.2 ∉ tsupport γ := fun hc => hz (hs hc)
    have he : ∀ᶠ y in 𝓝 z, y.2 ∉ tsupport γ :=
      continuous_snd.continuousAt ((isClosed_tsupport γ).isOpen_compl.mem_nhds ht)
    have heq : spatialField A γ ρ =ᶠ[𝓝 z] fun _ => 0 := he.mono (fun y hy =>
      spatialField_eq_zero_of_oneForm_eq_zero A γ ρ y (image_eq_zero_of_notMem_tsupport hy))
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [CompleteSpace E] in

theorem hasCompactSupport_spatialField
    (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ}
    (hγ : HasCompactSupport γ) (hρ : HasCompactSupport ρ) :
    HasCompactSupport (spatialField A γ ρ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hρ.prod hγ)
  intro z hz
  constructor
  · by_contra ht
    apply hz
    simp [spatialField, image_eq_zero_of_notMem_tsupport ht]
  · by_contra hx
    apply hz
    exact spatialField_eq_zero_of_oneForm_eq_zero A γ ρ z
      (image_eq_zero_of_notMem_tsupport hx)

theorem exists_lipschitz_spaceTimeField
    {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ} {U : Set E}
    (hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z)
    (hi : ∀ z, z.2 ∈ U → (A z).IsInvertible)
    (hγ : ContDiff ℝ ∞ γ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport γ ⊆ U)
    (hcγ : HasCompactSupport γ) (hcρ : HasCompactSupport ρ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun z => ((1 : ℝ), spatialField A γ ρ z)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_spatialField A hcγ hcρ)
    (contDiff_spatialField hA hi hγ hρ hs) (by simp)
  exact ⟨max 0 K, (LipschitzWith.const (1 : ℝ)).prodMk hK⟩

end
end Moser

namespace Moser

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u24} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def extendedOneForm (γ : E → E →L[ℝ] ℝ) (β : ℝ → ℝ) (z : ℝ × E) :
    (ℝ × E) →L[ℝ] ℝ :=
  β z.1 • (γ z.2).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem extendedOneForm_apply (γ : E → E →L[ℝ] ℝ) (β : ℝ → ℝ)
    (z a : ℝ × E) : extendedOneForm γ β z a = β z.1 * γ z.2 a.2 := rfl

theorem contDiff_extendedOneForm {γ : E → E →L[ℝ] ℝ} {β : ℝ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (extendedOneForm γ β) := by
  exact (hβ.comp contDiff_fst).smul ((hγ.comp contDiff_snd).clm_comp contDiff_const)

theorem fderiv_extendedOneForm {γ : E → E →L[ℝ] ℝ} {β : ℝ → ℝ} {z : ℝ × E}
    (hγ : DifferentiableAt ℝ γ z.2) (hβ : DifferentiableAt ℝ β z.1)
    (a b : ℝ × E) :
    fderiv ℝ (extendedOneForm γ β) z a b =
      deriv β z.1 * a.1 * γ z.2 b.2 + β z.1 * fderiv ℝ γ z.2 a.2 b.2 := by
  have hα : DifferentiableAt ℝ (extendedOneForm γ β) z :=
    (hβ.comp z differentiableAt_fst).smul
      ((hγ.comp z differentiableAt_snd).clm_comp (differentiableAt_const _))
  have he : fderiv ℝ (fun y => extendedOneForm γ β y b) z a =
      fderiv ℝ (extendedOneForm γ β) z a b := by
    rw [fderiv_clm_apply hα (differentiableAt_const b)]; simp
  rw [← he]
  simp only [extendedOneForm_apply]
  have hb : DifferentiableAt ℝ (fun y : ℝ × E => β y.1) z :=
    hβ.comp z differentiableAt_fst
  have hg : DifferentiableAt ℝ (fun y : ℝ × E => γ y.2 b.2) z :=
    (hγ.comp z differentiableAt_snd).clm_apply (differentiableAt_const b.2)
  rw [fderiv_fun_mul hb hg]
  rw [fderiv_fun_comp z hβ differentiableAt_fst]
  have hg' : DifferentiableAt ℝ (fun y : ℝ × E => γ y.2) z :=
    hγ.comp z differentiableAt_snd
  rw [fderiv_clm_apply hg' (differentiableAt_const b.2)]
  rw [fderiv_fun_comp z hγ differentiableAt_snd]
  simp [fderiv_eq_smul_deriv, fderiv_fst, fderiv_snd, mul_comm, add_comm]

def spatialTensor (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) (z : ℝ × E) : TwoTensor E :=
  W z.2 + β z.1 • exteriorD γ z.2

def spaceTimeTensor (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) (z : ℝ × E) : TwoTensor (ℝ × E) :=
  pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (W z.2) +
    exteriorD (extendedOneForm γ β) z

theorem contDiffAt_spatialTensor {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiffAt ℝ ∞ (spatialTensor W γ β) z := by
  have hd : ContDiff ℝ ∞ (exteriorD γ) :=
    contDiff_exteriorD hγ
  exact (hW.comp z contDiffAt_snd).add
    ((hβ.contDiffAt.comp z contDiffAt_fst).smul (hd.contDiffAt.comp z contDiffAt_snd))

theorem contDiffAt_spaceTimeTensor {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiffAt ℝ ∞ (spaceTimeTensor W γ β) z := by
  have hα := contDiff_extendedOneForm hγ hβ
  have hd : ContDiff ℝ ∞ (exteriorD (extendedOneForm γ β)) :=
    contDiff_exteriorD hα
  exact (contDiffAt_pullLinear (ContinuousLinearMap.snd ℝ ℝ E)
    (hW.comp z contDiffAt_snd)).add hd.contDiffAt

theorem spaceTimeTensor_apply {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hγ : DifferentiableAt ℝ γ z.2)
    (hβ : DifferentiableAt ℝ β z.1) (a b : ℝ × E) :
    spaceTimeTensor W γ β z a b = spatialTensor W γ β z a.2 b.2 +
      deriv β z.1 * (a.1 * γ z.2 b.2 - b.1 * γ z.2 a.2) := by
  simp only [spaceTimeTensor, add_apply, pullLinear_apply,
    ContinuousLinearMap.coe_snd', exteriorD_apply, fderiv_extendedOneForm hγ hβ,
    spatialTensor, smul_apply, smul_eq_mul]
  ring

theorem spaceTimeTensor_skew (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) {z : ℝ × E} (hW : ∀ a b, W z.2 a b = -W z.2 b a) (a b : ℝ × E) :
    spaceTimeTensor W γ β z a b = -spaceTimeTensor W γ β z b a := by
  simp only [spaceTimeTensor, add_apply, pullLinear_apply,
    ContinuousLinearMap.coe_snd']
  rw [hW a.2 b.2, exteriorD_skew (extendedOneForm γ β) z a b]
  ring

theorem spaceTimeTensor_closed {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β)
    (hclosed : ∀ a b c, fderiv ℝ W z.2 a b c +
      fderiv ℝ W z.2 b c a + fderiv ℝ W z.2 c a b = 0) (a b c : ℝ × E) :
    fderiv ℝ (spaceTimeTensor W γ β) z a b c +
      fderiv ℝ (spaceTimeTensor W γ β) z b c a +
      fderiv ℝ (spaceTimeTensor W γ β) z c a b = 0 := by
  have hα := contDiff_extendedOneForm hγ hβ
  have hd : ContDiff ℝ ∞ (exteriorD (extendedOneForm γ β)) :=
    contDiff_exteriorD hα
  have hp : ContDiffAt ℝ ∞ (fun y : ℝ × E =>
      pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (W y.2)) z :=
    contDiffAt_pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (hW.comp z contDiffAt_snd)
  have he := pullLinear_closed (ContinuousLinearMap.snd ℝ ℝ E) hW hclosed a b c
  have hf := exteriorD_closed (x := z) hα.contDiffAt a b c
  unfold spaceTimeTensor
  simp only [fderiv_fun_add (hp.differentiableAt (by simp))
    (hd.differentiable (by simp) z), add_apply]
  dsimp only [ContinuousLinearMap.coe_snd'] at he
  linarith

theorem spaceTimeTensor_kernel {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hγ : DifferentiableAt ℝ γ z.2)
    (hβ : DifferentiableAt ℝ β z.1)
    (hi : (spatialTensor W γ β z).IsInvertible)
    (hsk : ∀ a b, W z.2 a b = -W z.2 b a) :
    spaceTimeTensor W γ β z (1, spatialField (spatialTensor W γ β) γ (deriv β) z) = 0 := by
  have hs : ∀ a b, spatialTensor W γ β z a b = -spatialTensor W γ β z b a := by
    intro a b
    simp only [spatialTensor, add_apply, smul_apply,
      smul_eq_mul]
    rw [hsk a b, exteriorD_skew γ z.2 a b]; ring
  have hc := contract_spatialField γ (deriv β) z hi
  have hz := oneForm_spatialField γ (deriv β) z hi hs
  apply ContinuousLinearMap.ext
  intro a
  rw [spaceTimeTensor_apply hγ hβ]
  simp only [one_mul, hz, mul_zero, sub_zero]
  have hc' := congrArg (fun L : E →L[ℝ] ℝ => L a.2) hc
  simp only [smul_apply, smul_eq_mul] at hc'
  simp only [zero_apply]
  linarith

end
end Moser

open Set Filter
open scoped Topology ContDiff

namespace Moser

noncomputable section

def timeCutoff : ℝ → ℝ := Real.smoothTransition

theorem timeCutoff_smooth : ContDiff ℝ ∞ timeCutoff := Real.smoothTransition.contDiff

theorem timeCutoff_mem (t : ℝ) : timeCutoff t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

@[simp] theorem timeCutoff_zero : timeCutoff 0 = 0 := Real.smoothTransition.zero

@[simp] theorem timeCutoff_one : timeCutoff 1 = 1 := Real.smoothTransition.one

theorem timeCutoff_deriv_smooth : ContDiff ℝ ∞ (deriv timeCutoff) :=
  (show ContDiff ℝ (∞ + 1) timeCutoff by simpa using timeCutoff_smooth).deriv'

theorem timeCutoff_deriv_hasCompactSupport : HasCompactSupport (deriv timeCutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  intro t ht
  by_contra h
  have hd : deriv timeCutoff t = 0 := by
    rw [mem_Icc, not_and_or] at h
    rcases h with h | h
    · have hn : ∀ᶠ y in 𝓝 t, y < 0 := Iio_mem_nhds (lt_of_not_ge h)
      have he : timeCutoff =ᶠ[𝓝 t] fun _ => 0 :=
        hn.mono (fun y hy =>
          Real.smoothTransition.zero_of_nonpos hy.le)
      rw [he.deriv_eq, deriv_const]
    · have hn : ∀ᶠ y in 𝓝 t, 1 < y := Ioi_mem_nhds (lt_of_not_ge h)
      have he : timeCutoff =ᶠ[𝓝 t] fun _ => 1 :=
        hn.mono (fun y hy =>
          Real.smoothTransition.one_of_one_le hy.le)
      rw [he.deriv_eq, deriv_const]
  exact ht hd

end
end Moser

end LowerBoundInline

end OAI
