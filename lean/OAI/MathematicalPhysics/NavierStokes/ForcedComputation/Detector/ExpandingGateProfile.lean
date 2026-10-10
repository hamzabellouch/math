import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarCutoff

namespace OAI

/-! A fixed compact cutoff, rescaled to each expanding gate. Its exact
plateau has radius twice the gate radius, with support of radius three. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

private def unitGateBox : RationalBox 2 := ⟨fun _ => -1, fun _ => 1⟩

def gateCutoff (R : ℝ) (x : Plane) : ℝ :=
  PlanarHamiltonian.rectangleCutoff unitGateBox 1 (fun j => x j / R)

theorem gateCutoff_eq_profiles (R : ℝ) (x : Plane) :
    gateCutoff R x = closedCutoff (-3) (-2) 2 3 (x 0 / R) *
      closedCutoff (-3) (-2) 2 3 (x 1 / R) := by
  norm_num [gateCutoff, PlanarHamiltonian.rectangleCutoff, unitGateBox]

theorem gateCutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (gateCutoff R) := by
  apply (PlanarHamiltonian.rectangleCutoff_smooth unitGateBox 1).comp
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℝ ℝ j).div_const R

theorem gateCutoff_range (R : ℝ) (x : Plane) : gateCutoff R x ∈ Icc (0 : ℝ) 1 := by
  have h₀ := closedCutoff_range (-3) (-2) 2 3 (x 0 / R)
  have h₁ := closedCutoff_range (-3) (-2) 2 3 (x 1 / R)
  change 0 ≤ _ ∧ _ ≤ 1
  have he : gateCutoff R x = closedCutoff (-3) (-2) 2 3 (x 0 / R) *
      closedCutoff (-3) (-2) 2 3 (x 1 / R) := by
    norm_num [gateCutoff, PlanarHamiltonian.rectangleCutoff, unitGateBox]
  rw [he]
  refine ⟨mul_nonneg h₀.1 h₁.1, ?_⟩
  calc
    _ ≤ 1 * closedCutoff (-3) (-2) 2 3 (x 1 / R) := mul_le_mul_of_nonneg_right h₀.2 h₁.1
    _ ≤ 1 := by simpa only [one_mul] using h₁.2

theorem gateCutoff_one_near {R : ℝ} (hR : 0 < R) {x : Plane}
    (hx : ∀ j, |x j| < 2 * R) : gateCutoff R =ᶠ[𝓝 x] fun _ => 1 := by
  have hi : (fun j => x j / R) ∈ PlanarHamiltonian.rectanglePlateau unitGateBox 1 := by
    intro j
    have hl := (abs_lt.mp (hx j)).1
    have hu := (abs_lt.mp (hx j)).2
    dsimp [unitGateBox]
    norm_num only [Rat.cast_neg, Rat.cast_one]
    constructor
    · apply (lt_div_iff₀ hR).mpr
      linarith
    · apply (div_lt_iff₀ hR).mpr
      linarith
  have he : PlanarHamiltonian.rectangleCutoff unitGateBox 1 =ᶠ[𝓝 (fun j => x j / R)]
      fun _ => 1 :=
    Filter.eventually_of_mem ((PlanarHamiltonian.rectanglePlateau_open unitGateBox 1).mem_nhds hi)
      (fun _ hy => PlanarHamiltonian.rectangleCutoff_one (by norm_num) hy)
  have hc : Continuous (fun y : Plane => fun j => y j / R) :=
    by
      have hs := ((R⁻¹) • ContinuousLinearMap.id ℝ Plane).continuous
      convert hs using 1
      funext y j
      simp [div_eq_mul_inv, mul_comm]
  exact he.comp_tendsto hc.continuousAt

theorem gateCutoff_support {R : ℝ} (hR : 0 < R) :
    Function.support (gateCutoff R) ⊆ {x | ∀ j, |x j| ≤ 3 * R} := by
  intro x hx j
  have hs := PlanarHamiltonian.rectangleCutoff_support (R := unitGateBox)
    (by norm_num : (0 : ℚ) < 1) hx
  have hl := (hs j).1
  have hu := (hs j).2
  change ((-1 : ℚ) - 2 * 1 : ℚ) ≤ x j / R at hl
  change x j / R ≤ ((1 : ℚ) + 2 * 1 : ℚ) at hu
  norm_num at hl hu
  apply abs_le.mpr
  exact ⟨by have := (le_div_iff₀ hR).mp hl; linarith,
    by have := (div_le_iff₀ hR).mp hu; linarith⟩

theorem gateCutoff_tsupport {R : ℝ} (hR : 0 < R) :
    tsupport (gateCutoff R) ⊆ {x | ∀ j, |x j| ≤ 3 * R} := by
  apply closure_minimal (gateCutoff_support hR)
  have hc (j : Fin 2) : Continuous (fun x : Plane => |x j|) :=
    continuous_abs.comp
      (show ContDiff ℝ ∞ (fun x : Plane => x j) from contDiff_apply ℝ ℝ j).continuous
  have hs (j : Fin 2) : IsClosed {x : Plane | |x j| ≤ 3 * R} :=
    isClosed_le (hc j) continuous_const
  simpa only [ofPred_forall] using isClosed_iInter hs

theorem gateCutoff_compactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (gateCutoff R) := by
  have he : {x : Plane | ∀ j, |x j| ≤ 3 * R} =
      Icc (fun _ => -(3 * R)) (fun _ => 3 * R) := by
    ext x
    simp only [mem_ofPred_eq, abs_le, mem_Icc, Pi.le_def, forall_and]
  apply HasCompactSupport.intro (K := Icc (fun _ : Fin 2 => -(3 * R)) (fun _ => 3 * R))
    isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (he ▸ gateCutoff_support hR hn)

end ForcedComputation.ExpandingDetector

end

end OAI
