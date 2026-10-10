import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalHessian

namespace OAI

/-! Localized Derivations. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart

namespace ChartCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {U : Set E}

def realPart (κ : ChartCutoff U) : ChartCutoff U where
  val := SchwartzMap.postcompCLM (Complex.ofRealCLM.comp Complex.reCLM) κ.val
  compact := by
    apply HasCompactSupport.of_support_subset_isCompact κ.compact
    intro x hx
    apply subset_tsupport (κ : E → ℂ)
    intro h
    exact hx (by change ((κ x).re : ℂ) = 0; simp [h])
  support_sub := by
    apply Subset.trans _ κ.support_sub
    apply closure_mono
    intro x hx h
    exact hx (by change ((κ x).re : ℂ) = 0; simp [h])

@[simp] lemma realPart_apply (κ : ChartCutoff U) (x : E) : κ.realPart x = ((κ x).re : ℂ) := rfl

lemma realPart_support (κ : ChartCutoff U) :
    tsupport (κ.realPart : E → ℂ) ⊆ tsupport (κ : E → ℂ) := by
  apply closure_mono
  intro x hx h
  exact hx (by simp [h])
end ChartCutoff

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def localizedDerivative (p : ι) (v : EC d) : Smooth A →ₗ[ℝ] Smooth A :=
  (globalize (D.patch p).index (D.cutoff p).realPart).comp
    (((lineDerivOpCLM ℂ 𝓢(EC d, ℂ) v).restrictScalars ℝ).toLinearMap.comp
      (localizeLinear A (D.patch p).index (cutoffGlobal (D.patch p).index (D.outerCutoff p))
        (cutoffGlobal_support _ _)))

lemma localizedDerivative_bound (k : ℕ) (p : ι) (v : EC d) :
    D.localizers.BoundedCore ((k : ℝ)+1) (k : ℝ) (D.localizedDerivative p v) := by
  let q := (D.patch p).index
  let ρ := cutoffGlobal q (D.outerCutoff p)
  let hp := cutoffGlobal_support q (D.outerCutoff p)
  obtain ⟨B,hB,hb⟩ := globalize_integer_bound D.localizers q (D.cutoff p).realPart k
  obtain ⟨C,hC,hc⟩ := coreBound_deriv (s := (k : ℝ)+1) (t := (k : ℝ)) v (by linarith)
  obtain ⟨E,hE,he⟩ := D.localization_integer_bound q ρ hp (k+1)
  rw [Nat.cast_add, Nat.cast_one] at he
  refine ⟨B*(C*E),mul_nonneg hB (mul_nonneg hC hE),fun f => ?_⟩
  let w := localize A q ρ hp f
  change ‖D.localizers.embed (k : ℝ) (globalize q (D.cutoff p).realPart (∂_{v} w))‖ ≤ _
  calc
    _ ≤ B*‖schwartzCoord (k : ℝ) (∂_{v} w)‖ := hb _
    _ ≤ B*(C*‖schwartzCoord ((k : ℝ)+1) w‖) := mul_le_mul_of_nonneg_left (hc w) hB
    _ ≤ B*(C*(E*‖D.localizers.embed ((k : ℝ)+1) f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (he f) hC) hB
    _ = _ := by ring

lemma localizedDerivative_apply (p : ι) (v : EC d) (f : Smooth A) (x : X) :
    D.localizedDerivative p v f x =
      if x ∈ (A.euclideanChart (D.patch p).index).source then
        (D.cutoff p).realPart (A.euclideanChart (D.patch p).index x) *
          fderiv ℝ (f ∘ (A.euclideanChart (D.patch p).index).symm)
            (A.euclideanChart (D.patch p).index x) v else 0 := by
  let q := (D.patch p).index
  let e := A.euclideanChart q
  change globalize q (D.cutoff p).realPart
    (∂_{v} (localize A q (cutoffGlobal q (D.outerCutoff p)) (cutoffGlobal_support _ _) f)) x = _
  rw [globalize_apply]
  dsimp only [q]
  by_cases hx : x ∈ e.source
  all_goals dsimp only [e, q] at hx
  · simp only [ite_eq_left hx]
    by_cases hκ : (D.cutoff p).realPart (e x) = 0
    · rw [hκ,zero_mul,zero_mul]
    · rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      have hh := localize_cutoff_eventually q (D.cutoff p).realPart (D.outerCutoff p)
        (fun y hy => D.outerCutoff_one p y ((D.cutoff p).realPart_support hy))
        f (e.mapsTo hx) hκ
      rw [hh.fderiv_eq]
  · simp only [ite_eq_right hx]

lemma localizedDerivative_mul (p : ι) (v : EC d) (f h : Smooth A) :
    D.localizedDerivative p v (f.mul h) =
      (D.localizedDerivative p v f).mul h + f.mul (D.localizedDerivative p v h) := by
  apply Smooth.ext
  intro x
  rw [Smooth.add_apply]
  change D.localizedDerivative p v (f.mul h) x =
    D.localizedDerivative p v f x * h x + f x * D.localizedDerivative p v h x
  rw [D.localizedDerivative_apply, D.localizedDerivative_apply, D.localizedDerivative_apply]
  let e := A.euclideanChart (D.patch p).index
  by_cases hx : x ∈ e.source
  all_goals dsimp only [e] at hx
  · simp only [ite_eq_left hx]
    have hf := (f.smooth (D.patch p).index).contDiffAt (e.open_target.mem_nhds (e.mapsTo hx))
    have hh := (h.smooth (D.patch p).index).contDiffAt (e.open_target.mem_nhds (e.mapsTo hx))
    have he : ((f.mul h) ∘ e.symm) = (fun y => f (e.symm y) * h (e.symm y)) := rfl
    have hd := fderiv_fun_mul (hf.differentiableAt (by simp)) (hh.differentiableAt (by simp))
    dsimp only [e, Function.comp_apply] at hd
    rw [he]
    dsimp only [e]
    rw [hd]
    simp only [add_apply, smul_apply,
      smul_eq_mul, (A.euclideanChart (D.patch p).index).left_inv hx]
    ring
  · simp only [ite_eq_right hx, zero_mul, mul_zero, add_zero]

lemma localizedDerivative_const (p : ι) (v : EC d) (c : ℂ) :
    D.localizedDerivative p v (Smooth.const c) = 0 := by
  apply Smooth.ext
  intro x
  rw [D.localizedDerivative_apply]
  have he : ((Smooth.const c : Smooth A) ∘ (A.euclideanChart (D.patch p).index).symm) =
      (fun _ : EC d => c) := rfl
  rw [he, fderiv_const_apply]
  split_ifs <;> simp only [zero_apply, mul_zero, Smooth.zero_apply]

def completedDerivative (k : ℕ) (p : ι) (v : EC d) :
    D.localizers.Sobolev ((k : ℝ)+1) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  D.localizers.extendCore ((k : ℝ)+1) (k : ℝ) (D.localizedDerivative p v)

lemma completedDerivative_embed (k : ℕ) (p : ι) (v : EC d) (f : Smooth A) :
    D.completedDerivative k p v (D.localizers.embed ((k : ℝ)+1) f) =
      D.localizers.embed (k : ℝ) (D.localizedDerivative p v f) :=
  D.localizers.extendCore_embed (D.localizedDerivative_bound k p v) f

end GluingData
end GlobalElliptic

end
end

end OAI
