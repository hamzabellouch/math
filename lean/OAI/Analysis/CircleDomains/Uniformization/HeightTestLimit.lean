import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Compact test pairings converge for the locally bounded pointwise
limit of the actual continuous height functions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_test_integral_tendsto
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Continuous (f n))
    {v : EuclideanPlane → ℝ}
    (hp : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (v p)))
    (hb : ∀ K : Set EuclideanPlane, IsCompact K →
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖f n p‖ ≤ C)
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ p, f n p*ψ p) atTop (𝓝 (∫ p, v p*ψ p)) := by
  obtain ⟨C, hC⟩ := hb (tsupport ψ) hs.isCompact
  apply tendsto_integral_of_dominated_convergence (bound := fun p => C*‖ψ p‖)
  · intro n
    exact (hf n).aestronglyMeasurable.mul hψ.aestronglyMeasurable
  · exact (hψ.integrable_of_hasCompactSupport hs).norm.const_mul C
  · intro n
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ tsupport ψ
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n p hp) (norm_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hp, mul_zero, norm_zero, le_refl]
  · exact Eventually.of_forall (fun p => (hp p).mul_const (ψ p))

end CircleDomainRigidity

end

end OAI
