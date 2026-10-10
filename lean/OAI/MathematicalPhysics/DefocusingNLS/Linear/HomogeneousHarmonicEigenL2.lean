import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialSmoothL2

namespace OAI

/-! # Weighted radial L² control of actual generator eigenmodes

Smoothness is derived from the projected ODE, and the top radial derivative
is then identified with the completed Cartesian derivative contraction.
-/

open Set MeasureTheory Filter Topology
open scoped ContDiff Laplacian NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_eigenvector_harmonic_topL2 (a b : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (m : ℕ)
    (q : HomogeneousY a N) (Q : ℝ → ℂ)
    (hq : ∀ x : E, homogeneousPhysicalCLM a N ha ha1 hk q x = Q ‖x‖)
    (w : HomogeneousY a N × HomogeneousY a N) (lam : ℂ)
    (hw : ∀ t : ℝ≥0, homogeneousComplexLinearizedStep a b N ha ha1 hk m q t w =
      Complex.exp (((t : ℝ) : ℂ) * lam) • w)
    (Y : E → ℂ) (eta : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(eta / (‖x‖ ^ 2 : ℝ)) * Y x)
    (R : ℝ) (hR : 0 ≤ R) (hQ : ContDiffOn ℝ ∞ Q (Ioi R)) :
    let f := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk w.1 x)
    let g := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk w.2 x)
    ContDiffOn ℝ ∞ f (Ioi R) ∧ ContDiffOn ℝ ∞ g (Ioi R) ∧
      IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi R) ∧
      IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N g r‖ ^ 2) (Ioi R) := by
  let f := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk w.1 x)
  let g := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk w.2 x)
  obtain ⟨hf, hg, heq⟩ := homogeneous_eigenvector_harmonic_channels
    a b N ha ha1 hk m q Q hq w lam hw Y eta hY hRay hEigen
  obtain ⟨hfs, hgs⟩ := harmonicRadialEigenpair_contDiffOn a b m Q f g eta lam hf hg heq R hR hQ
  have hYs := continuous_harmonicSphere Y hY
  have hh := memLp_star_harmonicSphere Y hYs
  refine ⟨hfs, hgs, ?_, ?_⟩
  · dsimp only [f] at hfs
    rw [← homogeneous_harmonic_projection a N ha ha1 hk w.1 Y] at hfs ⊢
    exact homogeneousAngularProjection_iteratedDeriv_integrable a N ha ha1 hk
      (fun z => star (Y z.1)) hh w.1 R hR hfs
  · dsimp only [g] at hgs
    rw [← homogeneous_harmonic_projection a N ha ha1 hk w.2 Y] at hgs ⊢
    exact homogeneousAngularProjection_iteratedDeriv_integrable a N ha ha1 hk
      (fun z => star (Y z.1)) hh w.2 R hR hgs

end DefocusingNLS

end OAI
