import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureWeakStar
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledPressureTesting

namespace OAI

/-! Weak-star pressure convergence for the actual coupled inner profiles. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_pressure_weakstar (R l b : ℝ)
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
    (φ : ℝ → ℝ) (hφ : Integrable φ (radialPressureMeasure R)) :
    Tendsto (fun n => ∫ r, (H n r)^((P n).p-1)*φ r ∂radialPressureMeasure R) atTop
      (𝓝 (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*φ r ∂radialPressureMeasure R)) := by
  apply radial_pressure_weakstar_of_C1_testing R l b (by linarith) hlR.le
    (abs_le.mpr ⟨by linarith [hb.1],by linarith [hb.2]⟩)
    (fun n r => (H n r)^((P n).p-1)) (fun n => (hH n).1.continuous.pow _) _ _ φ hφ
  · intro n r hr
    have hpos : 0 ≤ H n r := le_trans (by norm_num : (0 : ℝ) ≤ 999/1000)
      ((P n).lo_lower.trans ((hH n).2.2.2.2.1 r hr).1.1)
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hpos _)]
    exact ((hH n).2.2.2.2.1 r hr).2.trans (by norm_num)
  · intro g g₁ hg hg₁ hgD
    exact radial_coupled_pressure_test_convergence R l b hRlow hRu hl hlR hlwidth hb
      F G hFc hGc hFI hGI hB P hR H hH hp hcT hbT hloT g g₁ hg hg₁ hgD

end DefocusingNLS

end OAI
