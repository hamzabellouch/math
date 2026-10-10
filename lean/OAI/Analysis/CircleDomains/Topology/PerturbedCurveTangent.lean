import OAI.Analysis.CircleDomains.Topology.SmallPerturbationJordan
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! The actual two-parameter deformation has a jointly continuous
classical tangent, including the original boundary at parameter zero. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma perturbedCurve_deriv {V : ℂ → ℂ} {γ : ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (hγ : ContDiff ℝ ∞ γ) (ρ t : ℝ) :
    deriv (fun s => γ s+ρ • V (γ s)) t =
      deriv γ t+ρ • deriv (V ∘ γ) t := by
  exact (((hγ.differentiable (by simp) t).hasDerivAt).add
    (((hV.comp hγ).differentiable (by simp) t).hasDerivAt.const_smul ρ)).deriv

lemma perturbedCurve_tangent_continuous {V : ℂ → ℂ} {γ : ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (hγ : ContDiff ℝ ∞ γ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun t => γ t+p.1 • V (γ t)) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (fun t => γ t+p.1 • V (γ t)) p.2) =
      (fun p => deriv γ p.2+p.1 • deriv (V ∘ γ) p.2) := by
    funext p
    exact perturbedCurve_deriv hV hγ _ _
  rw [he]
  exact ((hγ.continuous_deriv (by simp)).comp continuous_snd).add
    (continuous_fst.smul (((hV.comp hγ).continuous_deriv (by simp)).comp continuous_snd))

end CircleDomainRigidity

end

end OAI
