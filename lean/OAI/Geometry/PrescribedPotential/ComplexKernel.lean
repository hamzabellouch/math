import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexOperator

namespace OAI

/-! Complex Kernel. -/

section

 

noncomputable section
namespace GlobalElliptic
open Anticanonical SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma complexL_re (g : KaehlerMetric A) (f : Smooth A) (x : X) :
    (complexL g f x).re = (g.laplacian (f.part Complex.reCLM)).value x := by
  change (((g.laplacian (f.part Complex.reCLM)).value x : ℂ) +
    Complex.I * ((g.laplacian (f.part Complex.imCLM)).value x : ℂ)).re = _
  simp

lemma complexL_im (g : KaehlerMetric A) (f : Smooth A) (x : X) :
    (complexL g f x).im = (g.laplacian (f.part Complex.imCLM)).value x := by
  change (((g.laplacian (f.part Complex.reCLM)).value x : ℂ) +
    Complex.I * ((g.laplacian (f.part Complex.imCLM)).value x : ℂ)).im = _
  simp

lemma complexL_constant_rhs_zero [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (f : Smooth A) {c : ℂ}
    (hf : complexL g f = Smooth.const c) : c = 0 := by
  have hr : c.re = 0 := g.constant_rhs_eq_zero (f.part Complex.reCLM) (by
    intro i z hz
    rw [← g.laplacian_localExpression _ i hz]
    change (g.laplacian (f.part Complex.reCLM)).value ((A.chart i).symm z) = _
    rw [← complexL_re, hf]
    rfl)
  have hi : c.im = 0 := g.constant_rhs_eq_zero (f.part Complex.imCLM) (by
    intro i z hz
    rw [← g.laplacian_localExpression _ i hz]
    change (g.laplacian (f.part Complex.imCLM)).value ((A.chart i).symm z) = _
    rw [← complexL_im, hf]
    rfl)
  exact Complex.ext hr hi

lemma complexL_kernel [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (f : Smooth A) (hf : complexL g f = 0) :
    ∃ c : ℂ, f = Smooth.const c := by
  obtain ⟨r, hr⟩ := linearizedMongeAmpere_kernel d X A g (f.part Complex.reCLM) (by
    intro i z hz
    rw [← g.laplacian_localExpression _ i hz]
    change (g.laplacian (f.part Complex.reCLM)).value ((A.chart i).symm z) = _
    rw [← complexL_re, hf, Smooth.zero_apply, Complex.zero_re])
  obtain ⟨s, hs⟩ := linearizedMongeAmpere_kernel d X A g (f.part Complex.imCLM) (by
    intro i z hz
    rw [← g.laplacian_localExpression _ i hz]
    change (g.laplacian (f.part Complex.imCLM)).value ((A.chart i).symm z) = _
    rw [← complexL_im, hf, Smooth.zero_apply, Complex.zero_im])
  refine ⟨⟨r, s⟩, Smooth.ext (fun x => ?_)⟩
  exact Complex.ext (hr x) (hs x)

end GlobalElliptic

end
end

end OAI
