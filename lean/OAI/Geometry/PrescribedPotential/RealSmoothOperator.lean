import Mathlib
import OAI.Geometry.PrescribedPotential.NormalizedPoisson
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Real Smooth Operator. -/

section

 

noncomputable section
namespace Anticanonical.SourceSmooth.SmoothRealFunction
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
lemma ext_value {f h : SmoothRealFunction A} (he : f.value = h.value) : f = h := by
  cases f
  cases h
  cases he
  rfl
end Anticanonical.SourceSmooth.SmoothRealFunction
namespace GlobalElliptic
open Anticanonical SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma Smooth.ofReal_part_re (f : SmoothRealFunction A) :
    (Smooth.ofReal f).part Complex.reCLM = f :=
  SmoothRealFunction.ext_value rfl

lemma Smooth.ofReal_part_im (f : SmoothRealFunction A) :
    (Smooth.ofReal f).part Complex.imCLM = SmoothRealFunction.constant 0 :=
  SmoothRealFunction.ext_value rfl

lemma laplacian_constant (g : KaehlerMetric A) (c : ℝ) :
    g.laplacian (SmoothRealFunction.constant c) = SmoothRealFunction.constant 0 := by
  apply SmoothRealFunction.ext_value
  funext x
  obtain ⟨i, hi⟩ := A.covers x
  change g.laplacianValue (SmoothRealFunction.constant c) x = 0
  rw [g.laplacianValue_local _ i hi, g.linearizedMongeAmpere_constant]
  rfl

lemma complexL_ofReal (g : KaehlerMetric A) (f : SmoothRealFunction A) :
    complexL g (Smooth.ofReal f) = Smooth.ofReal (g.laplacian f) := by
  apply Smooth.ext
  intro x
  apply Complex.ext
  · rw [complexL_re, Smooth.ofReal_part_re]
    rfl
  · rw [complexL_im, Smooth.ofReal_part_im, laplacian_constant]
    rfl

lemma exists_real_smooth_poisson [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (x₀ : X) (f : RealSmooth A) :
    ∃ (u : RealSmooth A) (c : ℝ), u.val x₀ = 0 ∧
      complexL g u.val = f.val + Smooth.const (c : ℂ) := by
  obtain ⟨φ, b, hφ, he⟩ := normalizedPoisson d X A g x₀ f.source
  refine ⟨RealSmooth.ofReal φ, -b, ?_, ?_⟩
  · change (φ.value x₀ : ℂ) = 0
    rw [hφ, Complex.ofReal_zero]
  · change complexL g (Smooth.ofReal φ) = _
    rw [complexL_ofReal, ← RealSmooth.ofReal_source f]
    apply Smooth.ext
    intro x
    obtain ⟨i, hi⟩ := A.covers x
    have hh := he i (A.chart i x) ((A.chart i).mapsTo hi)
    have hl : (g.laplacian φ).value x = g.linearizedMongeAmpere φ i (A.chart i x) :=
      g.laplacianValue_local φ i hi
    have hf : f.source.localExpression i (A.chart i x) = f.source.value x := by
      change f.source.value ((A.chart i).symm (A.chart i x)) = _
      rw [(A.chart i).left_inv hi]
    rw [hf, ← hl] at hh
    change ((g.laplacian φ).value x : ℂ) = (f.source.value x : ℂ) + ((-b : ℝ) : ℂ)
    rw [← Complex.ofReal_add]
    congr 1
    linarith
end GlobalElliptic

end
end

end OAI
