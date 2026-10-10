import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.KahlerCauchySchwarz
import OAI.Geometry.PrescribedRicci.KahlerGreenIdentity
import OAI.Geometry.PrescribedRicci.KahlerPoissonL2

namespace OAI

/-! Kahler Poincare. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

theorem poincare (g : KaehlerMetric A) : ∃ P : ℝ, 0 < P ∧
    ∀ φ : SmoothRealFunction A, g.integral φ.value = 0 →
      g.integral (fun x => φ.value x ^ 2) ≤ P * g.integral (g.energy φ φ).value := by
  obtain ⟨K,hK,hpoisson⟩ := g.exists_meanZero_poisson_L2
  refine ⟨K+1, by linarith, fun φ hφ => ?_⟩
  obtain ⟨u,hLu,hU⟩ := hpoisson φ hφ
  let Iφ := g.integral (fun x => φ.value x ^ 2)
  let E := g.integral (g.energy φ φ).value
  let Eu := g.integral (g.energy u u).value
  have hI : 0 ≤ Iφ := g.integral_nonneg (fun _ => sq_nonneg _)
  have hE : 0 ≤ E := g.integral_nonneg (g.energy_nonneg _)
  have hEu : 0 ≤ Eu := g.integral_nonneg (g.energy_nonneg _)
  have hgreenU : g.integral (fun x => u.value x * φ.value x) = -Eu := by
    have hh := g.green_identity u u
    rw [hLu] at hh
    exact hh
  have hgreen : Iφ = - g.integral (g.energy φ u).value := by
    have hh := g.green_identity φ u
    rw [hLu] at hh
    simpa only [Iφ, pow_two] using hh
  have hEuSq : Eu ^ 2 ≤ K * Iφ ^ 2 := by
    have hh := g.integral_cauchySchwarz u.continuous φ.continuous
    rw [hgreenU, neg_sq] at hh
    calc
      Eu ^ 2 ≤ g.integral (fun x => u.value x ^ 2) * Iφ := hh
      _ ≤ (K * Iφ) * Iφ := mul_le_mul_of_nonneg_right hU hI
      _ = _ := by ring
  have hEuBound : Eu ≤ (K+1) * Iφ := by
    apply (sq_le_sq₀ hEu (mul_nonneg (by linarith) hI)).1
    calc
      Eu ^ 2 ≤ K * Iφ ^ 2 := hEuSq
      _ ≤ (K+1)^2 * Iφ^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg K]) (sq_nonneg Iφ)
      _ = _ := by ring
  have hfinal : Iφ ^ 2 ≤ (K+1) * E * Iφ := by
    calc
      Iφ ^ 2 = (g.integral (g.energy φ u).value) ^ 2 := by rw [hgreen, neg_sq]
      _ ≤ E * Eu := g.energy_cauchySchwarz φ u
      _ ≤ E * ((K+1)*Iφ) := mul_le_mul_of_nonneg_left hEuBound hE
      _ = _ := by ring
  change Iφ ≤ (K+1)*E
  by_cases hz : Iφ = 0
  · rw [hz]; exact mul_nonneg (by linarith) hE
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne hI (Ne.symm hz))).1 (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hfinal)

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
