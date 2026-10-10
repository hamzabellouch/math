import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenL2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicBounded

namespace OAI

/-! The actual physical realization supplies boundedness and top energy for a smooth channel pair. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_harmonic_pair_bounded (a : ℝ) (N : ℕ)
    (ha : 0<a) (ha1 : a<1) (hk : 8<(N : ℝ))
    (u : HomogeneousY a N × HomogeneousY a N) (Y : E → ℂ)
    (hY : ∀ x : E, x≠0 → ContDiffAt ℝ ∞ Y x) :
    let A := fun f : HomogeneousY a N =>
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk f x)
    ∃ M : ℝ, 0≤M ∧ ∀ r, ‖(A u.1 r,A u.2 r)‖≤M := by
  intro A
  obtain ⟨Mf,hMf,hf⟩ := homogeneous_harmonic_channel_bounded a N ha ha1 hk u.1 Y hY
  obtain ⟨Mg,hMg,hg⟩ := homogeneous_harmonic_channel_bounded a N ha ha1 hk u.2 Y hY
  refine ⟨max Mf Mg,hMf.trans (le_max_left _ _),?_⟩
  intro r
  rw [Prod.norm_def]
  exact max_le_max (hf r) (hg r)

theorem homogeneous_harmonic_pair_topL2 (a : ℝ) (N : ℕ)
    (ha : 0<a) (ha1 : a<1) (hk : 8<(N : ℝ))
    (u : HomogeneousY a N × HomogeneousY a N) (Y : E → ℂ)
    (hY : ∀ x : E, x≠0 → ContDiffAt ℝ ∞ Y x)
    (hf : ContDiffOn ℝ ∞
      (harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk u.1 x)) (Ioi 0))
    (hg : ContDiffOn ℝ ∞
      (harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk u.2 x)) (Ioi 0)) :
    let A := fun f : HomogeneousY a N =>
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk f x)
    IntegrableOn (fun r => r^11*‖iteratedDeriv N (A u.1) r‖^2) (Ioi 0) ∧
    IntegrableOn (fun r => r^11*‖iteratedDeriv N (A u.2) r‖^2) (Ioi 0) := by
  intro A
  have hh := memLp_star_harmonicSphere Y (continuous_harmonicSphere Y hY)
  constructor
  · dsimp only [A]
    rw [← homogeneous_harmonic_projection a N ha ha1 hk u.1 Y] at hf ⊢
    exact homogeneousAngularProjection_iteratedDeriv_integrable a N ha ha1 hk
      (fun z => star (Y z.1)) hh u.1 0 le_rfl hf
  · dsimp only [A]
    rw [← homogeneous_harmonic_projection a N ha ha1 hk u.2 Y] at hg ⊢
    exact homogeneousAngularProjection_iteratedDeriv_integrable a N ha ha1 hk
      (fun z => star (Y z.1)) hh u.2 0 le_rfl hg

end DefocusingNLS

end OAI
