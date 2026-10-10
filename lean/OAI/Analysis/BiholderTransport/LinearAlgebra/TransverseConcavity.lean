import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

def hessianValue (x : M) (p xi : TangentSpace 𝓘(ℝ, Model n) x) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ =>
    cost (riemannianExp x (t • xi)) (riemannianExp x p)) 0

lemma mtw_affine_line (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x)
    (s : ℝ) :
    mtw x (p + s • eta) xi eta = -(3 / 2 : ℝ) *
      iteratedDeriv 2 (fun t : ℝ => hessianValue x (p + t • eta) xi) s := by
  have hshift : (fun r : ℝ => hessianValue x ((p + s • eta) + r • eta) xi) =
      (fun r : ℝ => hessianValue x (p + (s + r) • eta) xi) := by
    ext r
    rw [add_smul, add_assoc]
  change -(3 / 2 : ℝ) * iteratedDeriv 2
    (fun r : ℝ => hessianValue x ((p + s • eta) + r • eta) xi) 0 = _
  rw [hshift, iteratedDeriv_comp_const_add 2
    (fun t : ℝ => hessianValue x (p + t • eta) xi) s]
  simp only [add_zero]

lemma WeakMTW.transverse_second_nonpos (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x) (s : ℝ)
    (hs : p + s • eta ∈ injectivityDomain x) (hortho : inner ℝ xi eta = 0) :
    iteratedDeriv 2 (fun t : ℝ => hessianValue x (p + t • eta) xi) s ≤ 0 := by
  have hh := hmtw x (p + s • eta) hs xi eta hortho
  rw [mtw_affine_line] at hh
  linarith

lemma WeakMTW.transverse_concaveOn (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hline : ∀ s ∈ interior D, p + s • eta ∈ injectivityDomain x)
    (hortho : inner ℝ xi eta = 0)
    (hcont : ContinuousOn (fun t : ℝ => hessianValue x (p + t • eta) xi) D)
    (hsmooth : ContDiffOn ℝ 2 (fun t : ℝ => hessianValue x (p + t • eta) xi)
      (interior D)) :
    ConcaveOn ℝ D (fun t : ℝ => hessianValue x (p + t • eta) xi) := by
  apply concaveOn_of_deriv2_nonpos hD hcont (hsmooth.differentiableOn (by norm_num))
  · exact (hsmooth.deriv_of_isOpen isOpen_interior (m := 1) (by norm_num)).differentiableOn
      (by norm_num)
  · intro s hs
    rw [← iteratedDeriv_eq_iterate]
    exact hmtw.transverse_second_nonpos x p xi eta s (hline s hs) hortho

end WeakMTWTransport
end

end OAI
