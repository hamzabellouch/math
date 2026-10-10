import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledPressureWeakStar
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureUnweighted

namespace OAI

/-! Full unweighted weak-star convergence of the actual inner pressure. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_pressure_weakstar_unweighted (R l b : ℝ)
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
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 ‖F R‖))
    (φ : ℝ → ℝ) (hφ : Integrable φ (volume.restrict (Icc 0 R))) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..R, (H n r)^((P n).p-1)*φ r) atTop
      (𝓝 (∫ r in (0 : ℝ)..R, (Iic l).indicator (fun _ : ℝ => b) r*φ r)) := by
  exact radial_weighted_weakstar_unweighted R (by linarith) _ _
    (fun g hg => radial_coupled_pressure_weakstar R l b hRlow hRu hl hlR hlwidth hb
      F G hFc hGc hFI hGI hB P hR H hH hp hcT hbT hloT g hg) φ hφ

end DefocusingNLS

end OAI
