import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.Bases

namespace OAI

/-!
# Countably many measure evaluations determine weak convergence

Finite unions from a countable open basis suffice for the Portmanteau
lower bound on every open set. This is used to connect the measurable
kernel evaluations to the weak topology, without assuming a measurable
selection of tangent frames.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

def finiteBasisUnion (F : Finset (countableBasis Y)) : Set Y :=
  ⋃ U ∈ F, (U.val : Set Y)

omit [MeasurableSpace Y] [OpensMeasurableSpace Y] in
lemma isOpen_finiteBasisUnion (F : Finset (countableBasis Y)) :
    IsOpen (finiteBasisUnion F) :=
  isOpen_biUnion fun U _ => isOpen_of_mem_countableBasis U.property

theorem tendsto_probability_of_finiteBasisUnion
    (μs : ℕ → ProbabilityMeasure Y) (μ : ProbabilityMeasure Y)
    (h : ∀ F : Finset (countableBasis Y),
      Tendsto (fun k => (μs k : Measure Y) (finiteBasisUnion F)) atTop
        (𝓝 ((μ : Measure Y) (finiteBasisUnion F)))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro U hU
  let I := {B : countableBasis Y // (B.val : Set Y) ⊆ U}
  let W : Finset I → Set Y := fun F => ⋃ B ∈ F, (B.val.val : Set Y)
  have hWU (F : Finset I) : W F ⊆ U := by
    intro x hx
    simp only [W, mem_iUnion] at hx
    obtain ⟨B, hB, hxB⟩ := hx
    exact B.property hxB
  have hmono : Monotone W := by
    intro F G hFG x hx
    simp only [W, mem_iUnion] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := hx
    exact ⟨B, hFG hB, hxB⟩
  have hunion : (⋃ F : Finset I, W F) = U := by
    apply subset_antisymm
    · exact iUnion_subset hWU
    · intro x hx
      obtain ⟨B, hB, hxB, hBU⟩ :=
        (isBasis_countableBasis Y).exists_subset_of_mem_open hx hU
      let i : I := ⟨⟨B, hB⟩, hBU⟩
      refine mem_iUnion.mpr ⟨{i}, ?_⟩
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by simp, hxB⟩⟩
  have hWbasis (F : Finset I) : W F = finiteBasisUnion (F.image fun B => B.val) := by
    ext x
    simp only [W, finiteBasisUnion, mem_iUnion, Finset.mem_image]
    constructor
    · rintro ⟨B, hB, hx⟩
      exact ⟨B.val, ⟨B, hB, rfl⟩, hx⟩
    · rintro ⟨B, ⟨C, hC, rfl⟩, hx⟩
      exact ⟨C, hC, hx⟩
  have hmeasure : (μ : Measure Y) U = ⨆ F : Finset I, (μ : Measure Y) (W F) := by
    rw [← hunion, hmono.measure_iUnion]
  rw [hmeasure]
  apply iSup_le
  intro F
  have hconv : Tendsto (fun k => (μs k : Measure Y) (W F)) atTop
      (𝓝 ((μ : Measure Y) (W F))) := by
    simpa only [hWbasis] using h (F.image fun B => B.val)
  calc
    (μ : Measure Y) (W F) = liminf (fun k => (μs k : Measure Y) (W F)) atTop :=
      hconv.liminf_eq.symm
    _ ≤ liminf (fun k => (μs k : Measure Y) U) atTop :=
      liminf_le_liminf (Eventually.of_forall fun k => measure_mono (hWU F))

/-- The coordinate map into the countable family of open-set tests is
measurable for every actual probability kernel. -/
theorem measurable_kernel_finiteBasisUnion
    {Z : Type*} [MeasurableSpace Z] (κ : ProbabilityTheory.Kernel Z Y)
    (F : Finset (countableBasis Y)) :
    Measurable (fun z => κ z (finiteBasisUnion F)) :=
  ProbabilityTheory.Kernel.measurable_coe κ (isOpen_finiteBasisUnion F).measurableSet

end DukePrimeDegree

end

end OAI
