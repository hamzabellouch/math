import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexBoundaryConvergence

namespace OAI

/-! Actual inner logarithmic derivatives converge to the free matching map. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_logarithmic_boundary_convergence (R l b : ℝ)
    (hRlow : (3+7/10000 : ℝ) ≤ R) (hRu : R ≤ (10/3 : ℝ))
    (hl : (3 : ℝ) ≤ l) (hlR : l < R) (hlwidth : R-l ≤ (1/1000 : ℝ))
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hFI : ∀ r ∈ Icc l R, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l R, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l R, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2)
    (P : ℕ → RadialInnerData) (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 6))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 ‖F R‖)) :
    Tendsto (fun n =>
      let Q := radialPolar (H n) (radialPhase (P n).c (radialClampedAmplitude R (H n)))
      deriv Q R/Q R) atTop (𝓝 (G R/F R)) := by
  have ht := radial_coupled_complex_boundary_convergence R l b hRlow hRu hl hlR hlwidth hb
    F G hFc hGc hFI hGI hB P hR H hH hp hcT hbT hloT
  have hF := (continuous_fst.tendsto (F R,G R)).comp ht
  have hG := (continuous_snd.tendsto (F R,G R)).comp ht
  have hFnz : F R ≠ 0 := by
    have hlo : (999/1000 : ℝ) ≤ ‖F R‖ := ge_of_tendsto' hloT (fun n => (P n).lo_lower)
    intro hzero
    rw [hzero,norm_zero] at hlo
    norm_num at hlo
  exact hG.div hF hFnz

end DefocusingNLS

end OAI
