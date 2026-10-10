import OAI.Geometry.NodalSets.Charts.SphereIntegratedFormComparison
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientNormConvergence
import OAI.Geometry.NodalSets.Spectral.SphereWeakResolvent

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
local instance sphereQuadraticLimitMeasurable : MeasurableSpace Base := borel Base
local instance sphereQuadraticLimitBorel : BorelSpace Base := ⟨rfl⟩

lemma tendsto_of_eventually_relative_comparison (a b : ℕ → ℝ) (A : ℝ)
    (ha : Tendsto a atTop (𝓝 A))
    (hcmp : ∀ eps > 0, ∀ᶠ j in atTop,
      (1-eps)*a j ≤ b j ∧ b j ≤ (1+eps)*a j) :
    Tendsto b atTop (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  let K := |A|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hAK : A < K := by dsimp [K]; linarith [le_abs_self A]
  have hd : 0 < eps/(2*K) := div_pos heps (mul_pos (by norm_num) hK)
  filter_upwards [hcmp (eps/(2*K)) hd, ha.eventually (gt_mem_nhds hAK),
    (Metric.tendsto_nhds.mp ha) (eps/2) (by positivity)] with j hj hbound hclose
  have herr : |b j-a j| ≤ (eps/(2*K))*a j := by
    rw [abs_le]
    constructor <;> nlinarith [hj.1,hj.2]
  have hscale : (eps/(2*K))*K=eps/2 := by field_simp
  have hsmall : |b j-a j| < eps/2 :=
    herr.trans_lt (by rw [← hscale]; exact mul_lt_mul_of_pos_left hbound hd)
  rw [Real.dist_eq] at hclose ⊢
  calc
    |b j-A| ≤ |b j-a j|+|a j-A| := abs_sub_le _ _ _
    _ < eps := by linarith

theorem sphere_finite_norm_quadratic_limit
    (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u : ℕ → SphereEnergySmooth d) (z : SphereEnergyHilbert d)
    (hz : Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereDirichletForm (b j).tensor
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (sphereCompletedDirichlet d z z)) ∧
    Tendsto (fun j ↦ sphereWeightedPairing (b j).density
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d z))) := by
  have hL := ((sphereEnergyL2Map d).continuous.tendsto z).comp hz
  change Tendsto (fun j ↦ sphereEnergyL2Map d (sphereEnergyToCompletion d (u j)))
    atTop (𝓝 (sphereEnergyL2Map d z)) at hL
  have hW : Tendsto (fun j ↦ sphereWeightedPairing d.density
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d z))) := by
    have h := hL.inner (𝕜 := ℝ) hL
    simp only [sphereEnergyL2Map_coe] at h
    convert h using 1
    funext j
    exact (sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le)
      _ _ (SphereEnergySmooth.toSmooth d (u j)).property.continuous
      (SphereEnergySmooth.toSmooth d (u j)).property.continuous).symm
  have hD : Tendsto (fun j ↦ sphereDirichletForm d.tensor
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (sphereCompletedDirichlet d z z)) := by
    have h := (hz.inner (𝕜 := ℝ) hz).sub (hL.inner (𝕜 := ℝ) hL)
    change Tendsto (fun j ↦ sphereCompletedDirichlet d
      (sphereEnergyToCompletion d (u j)) (sphereEnergyToCompletion d (u j)))
      atTop (𝓝 (sphereCompletedDirichlet d z z)) at h
    simpa only [sphereCompletedDirichlet_coe] using h
  have hcomp (eps : ℝ) (heps : 0 < eps) : ∀ᶠ j in atTop,
      (1-eps)*sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        sphereDirichletForm (b j).tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ∧
      sphereDirichletForm (b j).tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        (1+eps)*sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ∧
      (1-eps)*sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        sphereWeightedPairing (b j).density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ∧
      sphereWeightedPairing (b j).density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        (1+eps)*sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) := by
    obtain ⟨eta,heta,H⟩ := sphere_coefficient_relative_form_comparison P hcover
      d.tensor d.smooth d.symm d.pos d.density hd d.positive eps heps
    filter_upwards [hcoeff.eventually (gt_mem_nhds heta)] with j hj
    exact sphere_integrated_form_comparison d.tensor (b j).tensor d.smooth (b j).smooth
      d.symm (b j).symm d.pos (b j).pos d.density (b j).density d.continuous (b j).continuous eps
      (H (b j).tensor (b j).density (b j).smooth (b j).symm (b j).pos (hb j) hj)
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)).property
  constructor
  · apply tendsto_of_eventually_relative_comparison _ _ _ hD
    intro eps heps
    exact (hcomp eps heps).mono (fun j hj ↦ ⟨hj.1,hj.2.1⟩)
  · apply tendsto_of_eventually_relative_comparison _ _ _ hW
    intro eps heps
    exact (hcomp eps heps).mono (fun j hj ↦ hj.2.2)

end
end Yau.Target

end OAI
