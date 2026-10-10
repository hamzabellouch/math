import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderSolution
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyCalculus
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Scalar L2 representatives give integrable energy densities and finite
energy bounds on every closed time interval. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set

theorem CylinderContinuousL2.sub {F G : ℝ → Plane × ℝ → ℝ} {S : Set ℝ}
    (hF : CylinderContinuousL2 F S) (hG : CylinderContinuousL2 G S) :
    CylinderContinuousL2 (fun t y => F t y - G t y) S := by
  obtain ⟨U, hU, hUF⟩ := hF
  obtain ⟨V, hV, hVG⟩ := hG
  refine ⟨fun t => U t - V t, hU.sub hV, ?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_sub (U t) (V t), hUF t ht, hVG t ht] with y hsub hu hv
  simp only [hsub, hu, hv, Pi.sub_apply]

theorem cylinderL2_norm_sq (u : CylinderL2) {f : Plane × ℝ → ℝ}
    (hf : (fun x => u x) =ᵐ[cylinderMeasure] f) :
    ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂cylinderMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  change u x * u x = f x ^ 2
  rw [hx, pow_two]

theorem CylinderContinuousL2.memLp {F : ℝ → Plane × ℝ → ℝ} {S : Set ℝ}
    (hF : CylinderContinuousL2 F S) {t : ℝ} (ht : t ∈ S) :
    MemLp (F t) 2 cylinderMeasure := by
  obtain ⟨U, _, hUF⟩ := hF
  exact (memLp_congr_ae (hUF t ht)).mp (Lp.memLp (U t))

theorem CylinderContinuousL2.square_integrable {F : ℝ → Plane × ℝ → ℝ} {S : Set ℝ}
    (hF : CylinderContinuousL2 F S) {t : ℝ} (ht : t ∈ S) :
    Integrable (fun y => F t y ^ 2) cylinderMeasure := by
  have hm := hF.memLp ht
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm

theorem CylinderContinuousL2.square_integral_continuous {F : ℝ → Plane × ℝ → ℝ}
    {S : Set ℝ} (hF : CylinderContinuousL2 F S) :
    ContinuousOn (fun t => ∫ y, F t y ^ 2 ∂cylinderMeasure) S := by
  obtain ⟨U, hU, hUF⟩ := hF
  exact (hU.norm.pow 2).congr (fun t ht => (cylinderL2_norm_sq (U t) (hUF t ht)).symm)

theorem CylinderContinuousL2.uniform_square_integral {F : ℝ → Plane × ℝ → ℝ}
    {S : Set ℝ} (hF : CylinderContinuousL2 F S) (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ S, (∫ y, F t y ^ 2 ∂cylinderMeasure) ≤ B := by
  obtain ⟨B, hB⟩ := hS.bddAbove_image hF.square_integral_continuous
  exact ⟨max 0 B, le_max_left _ _, fun t ht =>
    (hB (mem_image_of_mem _ ht)).trans (le_max_right _ _)⟩

def differenceEnergy (u v : Velocity) (t : ℝ) : ℝ :=
  ∫ y, dot (u (t, atHeight y.1 y.2) - v (t, atHeight y.1 y.2))
    (u (t, atHeight y.1 y.2) - v (t, atHeight y.1 y.2)) ∂cylinderMeasure

def pressureDifferenceEnergy (p q : Pressure) (t : ℝ) : ℝ :=
  ∫ y, (p (t, atHeight y.1 y.2) - q (t, atHeight y.1 y.2)) ^ 2 ∂cylinderMeasure

theorem IsCylinderClassicalSolution.pressure_difference_integrable
    {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun y => (p (t, atHeight y.1 y.2) - q (t, atHeight y.1 y.2)) ^ 2)
      cylinderMeasure :=
  ((hu.pressure_h1 t ht).1.sub (hv.pressure_h1 t ht).1).square_integrable ⟨ht, le_rfl⟩

theorem IsCylinderClassicalSolution.pressure_difference_uniform
    {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, pressureDifferenceEnergy p q t ≤ B :=
  ((hu.pressure_h1 T hT).1.sub (hv.pressure_h1 T hT).1).uniform_square_integral
    isCompact_Icc

theorem IsCylinderClassicalSolution.difference_square_integrable
    {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) :
    Integrable (fun y =>
      (u (t, atHeight y.1 y.2) j - v (t, atHeight y.1 y.2) j) ^ 2) cylinderMeasure := by
  have hum := (hu.velocity_h2 t ht j).1.memLp ⟨ht, le_rfl⟩
  have hvm := (hv.velocity_h2 t ht j).1.memLp ⟨ht, le_rfl⟩
  have hm := hum.sub hvm
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm

theorem IsCylinderClassicalSolution.difference_energy_integrable
    {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun y => dot (u (t, atHeight y.1 y.2) - v (t, atHeight y.1 y.2))
      (u (t, atHeight y.1 y.2) - v (t, atHeight y.1 y.2))) cylinderMeasure := by
  simpa only [dot, Pi.sub_apply, pow_two] using
    (integrable_finsetSum Finset.univ (fun j _ =>
      hu.difference_square_integrable hv ht j))

theorem IsCylinderClassicalSolution.difference_energy_continuous
    {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (differenceEnergy u v) (Icc 0 T) := by
  have hc (j : Fin 3) :=
    ((hu.velocity_h2 T hT j).1.sub (hv.velocity_h2 T hT j).1).square_integral_continuous
  have he (t : ℝ) (ht : t ∈ Icc 0 T) : differenceEnergy u v t = ∑ j : Fin 3,
      ∫ y, (u (t, atHeight y.1 y.2) j - v (t, atHeight y.1 y.2) j) ^ 2
        ∂cylinderMeasure := by
    simp only [differenceEnergy, dot, Pi.sub_apply, ← pow_two]
    exact integral_finsetSum _ (fun j _ => hu.difference_square_integrable hv ht.1 j)
  exact (continuousOn_finsetSum _ (fun j _ => hc j)).congr he

theorem IsCylinderClassicalSolution.difference_energy_uniform
    {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, differenceEnergy u v t ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hu.difference_energy_continuous hv hT)
  exact ⟨max 0 B, le_max_left _ _, fun t ht =>
    (hB (mem_image_of_mem _ ht)).trans (le_max_right _ _)⟩

end ForcedComputation.VelocityDetector

end

end OAI
