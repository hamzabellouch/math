import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarPositivity

namespace OAI

/-! Scalar comparison and uniqueness from the maximum principle. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

theorem spatialD_sub {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (j : Fin 2) :
    spatialD j (fun x => f x - g x) = fun x => spatialD j f x - spatialD j g x := by
  funext x
  simp only [spatialD, fderiv_fun_sub (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x), sub_apply]

theorem scalarGenerator_sub {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (ν : ℝ) (a : Plane → Plane) (x : Plane) :
    scalarGenerator ν a (fun y => f y - g y) x =
      scalarGenerator ν a f x - scalarGenerator ν a g x := by
  have hl : scalarLaplacian (fun y => f y - g y) x =
      scalarLaplacian f x - scalarLaplacian g x := by
    unfold scalarLaplacian
    simp only [spatialD_sub hf hg]
    simp only [spatialD_sub (spatialD_smooth _ hf) (spatialD_smooth _ hg),
      Finset.sum_sub_distrib]
  simp only [scalarGenerator, hl, fderiv_fun_sub (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x), sub_apply]
  ring

theorem TorusScalarSolution.sub {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h k w v : ℝ → Plane → ℝ} {w₀ v₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀)
    (hv : TorusScalarSolution T ν a k v v₀) :
    TorusScalarSolution T ν a (fun t x => h t x - k t x)
      (fun t x => w t x - v t x) (fun x => w₀ x - v₀ x) := by
  refine ⟨hw.smooth.sub hv.smooth, ?_, ?_, ?_⟩
  · intro t ht x n
    dsimp only
    rw [hw.periodic t ht x n, hv.periodic t ht x n]
  · funext x
    rw [hw.initial, hv.initial]
  · intro t ht x
    have hd := (hw.equation t ht x).sub (hv.equation t ht x)
    convert hd using 1
    rw [scalarGenerator_sub (hw.slice_smooth ht) (hv.slice_smooth ht)]
    ring

theorem TorusScalarSolution.compare {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h k w v : ℝ → Plane → ℝ} {w₀ v₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀)
    (hv : TorusScalarSolution T ν a k v v₀) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (hh : ∀ t ∈ Icc 0 T, ∀ x, h t x ≤ k t x) (h₀ : ∀ x, w₀ x ≤ v₀ x) :
    ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ v t x := by
  have hp := (hv.sub hw).nonnegative hT hν
    (fun t ht x => sub_nonneg.mpr (hh t ht x))
    (fun x => sub_nonneg.mpr (h₀ x))
  exact fun t ht x => sub_nonneg.mp (hp t ht x)

theorem TorusScalarSolution.unique {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀)
    (hv : TorusScalarSolution T ν a h v w₀) (hT : 0 ≤ T) (hν : 0 ≤ ν) :
    ∀ t ∈ Icc 0 T, w t = v t := by
  intro t ht
  funext x
  exact le_antisymm
    (hw.compare hv hT hν (fun _ _ _ => le_rfl) (fun _ => le_rfl) t ht x)
    (hv.compare hw hT hν (fun _ _ _ => le_rfl) (fun _ => le_rfl) t ht x)

end ForcedComputation.VelocityDetector

end

end OAI
