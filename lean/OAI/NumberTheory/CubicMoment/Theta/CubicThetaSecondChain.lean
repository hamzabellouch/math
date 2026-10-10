import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth

namespace OAI

/-! The real-to-complex second chain rule used for a smooth cutoff of
an arithmetic cusp height. -/
noncomputable section
open Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaSecondChain {f : ℝ → ℂ} {h : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f (h x)) (hh : ContDiffAt ℝ 2 h x) :
    deriv (deriv (f ∘ h)) x=(deriv h x)^2 • deriv (deriv f) (h x)+
      deriv (deriv h) x • deriv f (h x) := by
  have hf' : DifferentiableAt ℝ (deriv f) (h x) :=
    (hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hh' : DifferentiableAt ℝ (deriv h) x :=
    (hh.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hfe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f (h y) :=
    hh.continuousAt.eventually ((hf.eventually (by norm_num)).mono
      (fun _ hy => hy.differentiableAt (by norm_num)))
  have hhe : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y :=
    (hh.eventually (by norm_num)).mono (fun _ hy => hy.differentiableAt (by norm_num))
  have he : deriv (f ∘ h) =ᶠ[𝓝 x] (fun y => deriv h y • deriv f (h y)) := by
    filter_upwards [hfe,hhe] with y hfy hhy
    exact deriv.scomp y hfy hhy
  rw [he.deriv_eq]
  have hd := hh'.hasDerivAt.smul
    (hf'.hasDerivAt.scomp x (hh.differentiableAt (by norm_num)).hasDerivAt)
  simpa only [Pi.smul_def',Function.comp_def,smul_smul,← pow_two,add_comm] using hd.deriv

end CubicFirstMoment

end

end OAI
