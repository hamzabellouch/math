import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarHamiltonian
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Extension

namespace OAI

/-! Explicit rational collars for compact planar Hamiltonian pulses. -/

noncomputable section

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set Filter
open scoped Topology ContDiff

def rectangleCutoff (R : RationalBox 2) (δ : ℚ) (x : Plane) : ℝ :=
  letI := ShearFlows.neZeroTwo
  letI := ShearFlows.twoAtLeastTwo
  closedCutoff (R.lower 0 - 2 * δ) (R.lower 0 - δ)
      (R.upper 0 + δ) (R.upper 0 + 2 * δ) (x 0) *
    closedCutoff (R.lower 1 - 2 * δ) (R.lower 1 - δ)
      (R.upper 1 + δ) (R.upper 1 + 2 * δ) (x 1)

def rectangleCollar (R : RationalBox 2) (δ : ℚ) : RationalBox 2 :=
  ⟨fun j => R.lower j - 2 * δ, fun j => R.upper j + 2 * δ⟩

def rectanglePlateau (R : RationalBox 2) (δ : ℚ) : Set Plane :=
  {x | ∀ j, (R.lower j : ℝ) - δ < x j ∧ x j < (R.upper j : ℝ) + δ}

theorem rectangleCutoff_smooth (R : RationalBox 2) (δ : ℚ) :
    ContDiff ℝ ∞ (rectangleCutoff R δ) := by
  exact ((closedCutoff_smooth _ _ _ _).comp (contDiff_apply ℝ ℝ 0)).mul
    ((closedCutoff_smooth _ _ _ _).comp (contDiff_apply ℝ ℝ 1))

theorem rectanglePlateau_open (R : RationalBox 2) (δ : ℚ) :
    IsOpen (rectanglePlateau R δ) := by
  have he : rectanglePlateau R δ =
      ⋂ j : Fin 2, {x : Plane | (R.lower j : ℝ) - δ < x j ∧ x j < (R.upper j : ℝ) + δ} := by
    ext x
    simp [rectanglePlateau]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt continuous_const (continuous_apply j)).inter
    (isOpen_lt (continuous_apply j) continuous_const)

theorem mem_rectanglePlateau {R : RationalBox 2} {δ : ℚ} (hδ : 0 < δ)
    {x : Plane} (hx : x ∈ R.carrier) : x ∈ rectanglePlateau R δ := by
  have hp : (0 : ℝ) < δ := by exact_mod_cast hδ
  intro j
  constructor <;> linarith [(hx j).1, (hx j).2]

theorem rectangleCutoff_one {R : RationalBox 2} {δ : ℚ} (hδ : 0 < δ)
    {x : Plane} (hx : x ∈ rectanglePlateau R δ) : rectangleCutoff R δ x = 1 := by
  have ho (j : Fin 2) : (R.lower j - 2 * δ : ℚ) < (R.lower j - δ : ℚ) ∧
      (R.upper j + δ : ℚ) < (R.upper j + 2 * δ : ℚ) := by constructor <;> linarith
  have he (j : Fin 2) : closedCutoff (R.lower j - 2 * δ) (R.lower j - δ)
      (R.upper j + δ) (R.upper j + 2 * δ) (x j) = 1 := by
    apply closedCutoff_plateau
    · exact_mod_cast (ho j).1
    · exact_mod_cast (ho j).2
    · exact ⟨(hx j).1.le, (hx j).2.le⟩
  exact (show rectangleCutoff R δ x = 1 * 1 from congrArg₂ (· * ·) (he 0) (he 1)).trans
    (one_mul 1)

theorem rectangleCutoff_one_near {R : RationalBox 2} {δ : ℚ} (hδ : 0 < δ)
    {x : Plane} (hx : x ∈ R.carrier) : rectangleCutoff R δ =ᶠ[𝓝 x] fun _ => 1 :=
  Filter.eventually_of_mem ((rectanglePlateau_open R δ).mem_nhds (mem_rectanglePlateau hδ hx))
    (fun _ hy => rectangleCutoff_one hδ hy)

theorem rectangleCutoff_support {R : RationalBox 2} {δ : ℚ} (hδ : 0 < δ) :
    Function.support (rectangleCutoff R δ) ⊆ (rectangleCollar R δ).carrier := by
  intro x hx
  have hn : rectangleCutoff R δ x ≠ 0 := hx
  have h₀ : closedCutoff (R.lower 0 - 2 * δ) (R.lower 0 - δ)
      (R.upper 0 + δ) (R.upper 0 + 2 * δ) (x 0) ≠ 0 :=
    left_ne_zero_of_mul hn
  have h₁ : closedCutoff (R.lower 1 - 2 * δ) (R.lower 1 - δ)
      (R.upper 1 + δ) (R.upper 1 + 2 * δ) (x 1) ≠ 0 :=
    right_ne_zero_of_mul hn
  have ho (j : Fin 2) : (R.lower j - 2 * δ : ℝ) < (R.lower j - δ : ℝ) ∧
      (R.upper j + δ : ℝ) < (R.upper j + 2 * δ : ℝ) := by
    have hp : (0 : ℝ) < δ := by exact_mod_cast hδ
    constructor <;> linarith
  have h₀' := closedCutoff_support (ho 0).1 (ho 0).2 h₀
  have h₁' := closedCutoff_support (ho 1).1 (ho 1).2 h₁
  intro j
  fin_cases j
  · dsimp [rectangleCollar]
    push_cast
    constructor <;> linarith [h₀'.1, h₀'.2]
  · dsimp [rectangleCollar]
    push_cast
    constructor <;> linarith [h₁'.1, h₁'.2]

theorem rectangleCollar_compact (R : RationalBox 2) (δ : ℚ) :
    IsCompact (rectangleCollar R δ).carrier := by
  have he : (rectangleCollar R δ).carrier =
      Icc (fun j => ((rectangleCollar R δ).lower j : ℝ))
        (fun j => ((rectangleCollar R δ).upper j : ℝ)) := by
    ext x
    simp only [RationalBox.carrier, mem_ofPred_eq, mem_Icc, Pi.le_def, forall_and]
  rw [he]
  exact isCompact_Icc

theorem rectangleCutoff_compactSupport {R : RationalBox 2} {δ : ℚ} (hδ : 0 < δ) :
    HasCompactSupport (rectangleCutoff R δ) := by
  apply HasCompactSupport.intro (rectangleCollar_compact R δ)
  intro x hx
  by_contra hn
  exact hx (rectangleCutoff_support hδ hn)

/-- A polynomial Hamiltonian cut off by this explicit collar gives a smooth,
compact, divergence-free, mean-zero planar field with the exact local motion. -/
theorem rectangle_field_properties {R : RationalBox 2} {δ : ℚ} (hδ : 0 < δ)
    {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (field (fun x => rectangleCutoff R δ x * H x)) ∧
    HasCompactSupport (field (fun x => rectangleCutoff R δ x * H x)) ∧
    (∀ x, divergence (field (fun x => rectangleCutoff R δ x * H x)) x = 0) ∧
    (∫ x, field (fun y => rectangleCutoff R δ y * H y) x) = 0 ∧
    (∀ x ∈ R.carrier, field (fun y => rectangleCutoff R δ y * H y) x = field H x) := by
  have hs := (rectangleCutoff_smooth R δ).mul hH
  have hc : HasCompactSupport (fun x => rectangleCutoff R δ x * H x) :=
    (rectangleCutoff_compactSupport hδ).mul_right
  exact ⟨field_smooth hs, field_compactSupport hc, field_divergence hs,
    field_integral_eq_zero hs hc, fun _ hx => field_cutoff_plateau _ _ (rectangleCutoff_one_near hδ hx)⟩

end ForcedComputation.PlanarHamiltonian

end

end OAI
