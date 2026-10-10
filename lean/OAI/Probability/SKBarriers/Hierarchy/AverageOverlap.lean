import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.AverageReplica
import OAI.Probability.SKBarriers.Scalar.OverlapBoundArithmetic

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem block_average_overlap_concentration {D N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b)
    (hsmall : (k : ℝ)/Real.sqrt ((N : ℝ)*δ) ≤ 1) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let v : Config N → Fin N → ℝ := fun s i => spin (s i)
    (∑ j : Fin (k+1), ((k+1 : ℕ) : ℝ)⁻¹*hierarchyOverlapError n m U v (blockLevel D N k j)) ≤
      20*((k : ℝ)/Real.sqrt ((N : ℝ)*δ)+1/Real.sqrt (k : ℝ)) := by
  have H := block_average_overlap_explicit hN I a Δ hδ hΔ
  have A := overlap_error_arithmetic (k := (k : ℝ)) (v := (N : ℝ)*δ)
    (by exact_mod_cast Nat.succ_le_iff.mpr hk) (by positivity) hsmall
  simp only [Nat.cast_add,Nat.cast_one] at H
  simpa only [Nat.cast_add,Nat.cast_one] using H.trans A
end SK.Analytic

end
end

end

end OAI
