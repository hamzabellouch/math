import OAI.MeasureTheory.Falconer.Estimates.SourceAssemblyParameters
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! # A fixed compactly supported scalar cutoff for the assembly -/

namespace Falconer
open Set
open scoped SchwartzMap ContDiff

theorem exists_scalar_assembly_cutoff :
    ∃ (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ), (∀ r, φ r = (Ψ r : ℂ)) ∧
      Measurable Ψ ∧ ContDiff ℝ ∞ Ψ ∧ (∀ r, 0 ≤ Ψ r) ∧
      (∀ r ≤ 0, Ψ r = 0) ∧ (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) ∧
      (∀ r, Ψ r ≤ 1) ∧ (∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) := by
  let Ψ := PlanarFalconer.assemblyShellBump
  let φ : 𝓢(ℝ,ℂ) :=
    (Ψ.hasCompactSupport.toSchwartzMap Ψ.contDiff).postcompCLM Complex.ofRealCLM
  have hsupp (r : ℝ) (hr : Ψ r ≠ 0) : r ∈ Ioo (1/4:ℝ) 4 := by
    have hh : dist r (5/4:ℝ) < 1 := by
      by_contra hn
      exact hr (Ψ.zero_of_le_dist (not_lt.mp hn))
    rw [Real.dist_eq,abs_lt] at hh
    constructor <;> linarith
  refine ⟨φ,Ψ,fun _ => rfl,Ψ.continuous.measurable,Ψ.contDiff,fun _ => Ψ.nonneg,?_,?_,
    fun _ => Ψ.le_one,hsupp⟩
  · intro r hr
    by_contra hn
    have hh := (hsupp r hn).1
    linarith
  · intro r hr
    have hmem : r ∈ Metric.closedBall (5/4:ℝ) Ψ.rIn := by
      change dist r (5/4:ℝ) ≤ 3/4
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [hr.1,hr.2]
    rw [Ψ.one_of_mem_closedBall hmem]

end Falconer

end OAI
