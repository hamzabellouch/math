import Mathlib
import OAI.Geometry.PrescribedPotential.ChartTransport
import OAI.Geometry.PrescribedPotential.GlobalSobolev

namespace OAI

/-! Global Extension. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff SchwartzMap Classical

namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X]
  {A : ComplexAtlas d X}

 
def extendFun (i : Fin A.count) (f : EC d → ℂ) (x : X) : ℂ :=
  if x ∈ (A.euclideanChart i).source then f (A.euclideanChart i x) else 0

lemma extendFun_apply {i : Fin A.count} (f : EC d → ℂ) {x : X}
    (hx : x ∈ (A.euclideanChart i).source) :
    extendFun (A := A) i f x = f (A.euclideanChart i x) := ite_eq_left hx

lemma extendFun_support (i : Fin A.count) (f : EC d → ℂ) :
    Function.support (extendFun (A := A) i f) ⊆
      (A.euclideanChart i).symm '' tsupport f := by
  intro x hx
  have hn : extendFun (A := A) i f x ≠ 0 := hx
  by_cases hi : x ∈ (A.euclideanChart i).source
  · rw [extendFun_apply f hi] at hn
    exact ⟨A.euclideanChart i x, subset_tsupport f hn, (A.euclideanChart i).left_inv hi⟩
  · exact (hn (ite_eq_right hi)).elim

variable [T2Space X]

lemma extendFun_smooth (i : Fin A.count) (f : EC d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (A.euclideanChart i).target) :
    ∀ j, ContDiffOn ℝ ∞ (extendFun (A := A) i f ∘ (A.euclideanChart j).symm)
      (A.euclideanChart j).target := by
  intro j y hy
  let e := A.euclideanChart i
  let q := A.euclideanChart j
  let K := e.symm '' tsupport f
  have hK : IsCompact K := hc.image_of_continuousOn (e.symm.continuousOn.mono hs)
  have hKi : K ⊆ e.source := by rintro x ⟨z, hz, rfl⟩; exact e.symm.mapsTo (hs hz)
  by_cases hi : q.symm y ∈ e.source
  · let t := q.symm.trans e
    have ht : y ∈ t.source := ⟨hy, hi⟩
    have hsm := (hf.contDiffAt (x := t y)).comp y
      ((A.euclidean_transition_smooth j i).contDiffAt (t.open_source.mem_nhds ht))
    apply (hsm.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [t.open_source.mem_nhds ht] with z hz
    exact ite_eq_left hz.2
  · have hnot : q.symm y ∉ K := fun hk => hi (hKi hk)
    have hn := (q.symm.continuousAt hy) (hK.isClosed.isOpen_compl.mem_nhds hnot)
    apply ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with z hz
    exact Function.notMem_support.mp (fun hp => hz (extendFun_support i f hp))

 
def extend (i : Fin A.count) (f : EC d → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (A.euclideanChart i).target) : Smooth A :=
  ⟨extendFun i f, extendFun_smooth i f hf hc hs⟩

lemma extend_tsupport (i : Fin A.count) (f : EC d → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (A.euclideanChart i).target) :
    tsupport (extend i f hf hc hs : X → ℂ) ⊆ (A.euclideanChart i).symm '' tsupport f := by
  apply closure_minimal (extendFun_support i f)
  exact (hc.image_of_continuousOn ((A.euclideanChart i).symm.continuousOn.mono hs)).isClosed

 
def globalize (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) :
    𝓢(EC d, ℂ) →ₗ[ℝ] Smooth A where
  toFun f := extend i (fun y => κ y * f y)
    ((κ.val.smooth ⊤).mul (f.smooth ⊤)) (κ.product_compact f)
    ((κ.product_tsupport (A.euclideanChart i).open_target (f.smooth ⊤).contDiffOn).trans κ.support_sub)
  map_add' f h := by
    apply Smooth.ext
    intro x
    change extendFun i (fun y => κ y * (f + h) y) x =
      extendFun i (fun y => κ y * f y) x + extendFun i (fun y => κ y * h y) x
    by_cases hx : x ∈ (A.euclideanChart i).source
    · simp only [extendFun, ite_eq_left hx, add_apply]
      exact mul_add _ _ _
    · simp only [extendFun, ite_eq_right hx, add_zero]
  map_smul' c f := by
    apply Smooth.ext
    intro x
    change extendFun i (fun y => κ y * (c • f) y) x =
      c • extendFun i (fun y => κ y * f y) x
    by_cases hx : x ∈ (A.euclideanChart i).source
    · simp only [extendFun, ite_eq_left hx, smul_apply,
        Complex.real_smul]
      ring
    · simp only [extendFun, ite_eq_right hx, smul_zero]

@[simp] lemma globalize_apply (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target)
    (f : 𝓢(EC d, ℂ)) (x : X) :
    globalize i κ f x = if x ∈ (A.euclideanChart i).source then
      κ (A.euclideanChart i x) * f (A.euclideanChart i x) else 0 := rfl

lemma globalize_tsupport (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target)
    (f : 𝓢(EC d, ℂ)) :
    tsupport (globalize i κ f : X → ℂ) ⊆
      (A.euclideanChart i).symm '' tsupport (κ : EC d → ℂ) := by
  exact (extend_tsupport i (fun y => κ y * f y)
    ((κ.val.smooth ⊤).mul (f.smooth ⊤)) (κ.product_compact f)
    ((κ.product_tsupport (A.euclideanChart i).open_target (f.smooth ⊤).contDiffOn).trans
      κ.support_sub)).trans (image_mono
    (κ.product_tsupport (A.euclideanChart i).open_target (f.smooth ⊤).contDiffOn))

end GlobalElliptic

end
end

end OAI
