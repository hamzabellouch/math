import OAI.Analysis.CircleDomains.Sobolev.LocalArgumentBranch
import Mathlib.Geometry.Manifold.Instances.Sphere

namespace OAI

/-! A smooth period-one plane curve descends smoothly to the geometric
unit circle. The proof uses actual local logarithmic branches. -/
open Set Function Filter
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma toCircle_normalizedArgument (z : Circle) :
    AddCircle.toCircle (normalizedArgument (z : ℂ)) = z := by
  rw [normalizedArgument_eq, AddCircle.toCircle_apply_mk]
  have he : 2 * Real.pi / (1 : ℝ) * (Complex.arg (z : ℂ) / (2*Real.pi)) =
      Complex.arg (z : ℂ) := by field_simp
  rw [he, Circle.exp_arg]

lemma normalizedArgument_circleExp (t : ℝ) :
    normalizedArgument (Circle.exp (2*Real.pi*t) : ℂ) = (t : UnitAddCircle) := by
  apply AddCircle.injective_toCircle one_ne_zero
  rw [toCircle_normalizedArgument, AddCircle.toCircle_apply_mk, div_one]

lemma normalizedArgument_injective_circle :
    Injective (fun z : Circle => normalizedArgument (z : ℂ)) := by
  intro z w h
  have he := congrArg AddCircle.toCircle h
  simpa only [toCircle_normalizedArgument] using he

def periodicCircleDescent {γ : ℝ → ℂ} (hγ : Periodic γ 1) (z : Circle) : ℂ :=
  hγ.lift (normalizedArgument (z : ℂ))

lemma periodicCircleDescent_exp {γ : ℝ → ℂ} (hγ : Periodic γ 1) (t : ℝ) :
    periodicCircleDescent hγ (Circle.exp (2*Real.pi*t)) = γ t := by
  rw [periodicCircleDescent, normalizedArgument_circleExp, hγ.lift_coe]

lemma periodicCircleDescent_smooth {γ : ℝ → ℂ} (hγ : Periodic γ 1)
    (hs : ContDiff ℝ ∞ γ) : ContMDiff (𝓡 1) (𝓘(ℝ,ℂ)) ∞ (periodicCircleDescent hγ) := by
  let : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by norm_num⟩
  have hcoe : ContMDiff (𝓡 1) (𝓘(ℝ,ℂ)) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  intro z
  let u : ℂ → ℂ := γ ∘ localArgumentBranch (z : ℂ)
  have hu : ContDiffAt ℝ ∞ u (z : ℂ) :=
    hs.contDiffAt.comp _ (localArgumentBranch_smooth z.coe_ne_zero)
  have he : periodicCircleDescent hγ =ᶠ[𝓝 z] (fun w : Circle => u (w : ℂ)) := by
    filter_upwards [] with w
    dsimp [periodicCircleDescent, u, Function.comp_def]
    rw [← localArgumentBranch_projects z.coe_ne_zero w.coe_ne_zero, hγ.lift_coe]
  exact (hu.contMDiffAt.comp z hcoe.contMDiffAt).congr_of_eventuallyEq he

lemma periodicCircleDescent_injective {γ : ℝ → ℂ} (hγ : Periodic γ 1)
    (hi : InjOn γ (Ico 0 1)) : Injective (periodicCircleDescent hγ) := by
  intro z w he
  let r := AddCircle.equivIco 1 0 (normalizedArgument (z : ℂ))
  let s := AddCircle.equivIco 1 0 (normalizedArgument (w : ℂ))
  have hr : (r.val : UnitAddCircle) = normalizedArgument (z : ℂ) := AddCircle.coe_equivIco
  have hs : (s.val : UnitAddCircle) = normalizedArgument (w : ℂ) := AddCircle.coe_equivIco
  have he' : γ r.val = γ s.val := by
    simpa only [periodicCircleDescent, ← hr, ← hs, hγ.lift_coe] using he
  have hrs := hi (by simpa only [zero_add] using r.property)
    (by simpa only [zero_add] using s.property) he'
  exact normalizedArgument_injective_circle
    (hr.symm.trans ((congrArg (fun t : ℝ => (t : UnitAddCircle)) hrs).trans hs))

lemma periodicCircleDescent_range {γ : ℝ → ℂ} (hγ : Periodic γ 1) :
    range (periodicCircleDescent hγ) = range γ := by
  apply Subset.antisymm
  · rintro y ⟨z,rfl⟩
    let r := AddCircle.equivIco 1 0 (normalizedArgument (z : ℂ))
    refine ⟨r.val,?_⟩
    have hr : (r.val : UnitAddCircle) = normalizedArgument (z : ℂ) := AddCircle.coe_equivIco
    rw [periodicCircleDescent, ← hr, hγ.lift_coe]
  · rintro y ⟨t,rfl⟩
    exact ⟨Circle.exp (2*Real.pi*t),periodicCircleDescent_exp hγ t⟩

end CircleDomainRigidity

end

end OAI
