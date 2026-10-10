import OAI.GroupTheory.PolycyclicRecognition.Geometry.BasisAdjointNilpotent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentConjugationDecay

namespace OAI

/-! # Interior slack for conjugation in varying actual coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology

/-- A sufficiently large exponential margin survives conjugation by every
expanded-box coordinate, uniformly over a bounded family of actual brackets.
The exact exponential-conjugation law is provided by the existing faithful
realization theorem in the application. -/
theorem coordinate_conjugation_tendsto_zero
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n m c : ℕ}
    [Nonempty (Fin n)]
    (b : ℝ → Basis (Fin n) ℝ L)
    (hk : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (a : DynkinCoefficients c 2)
    (hconj : ∀ r, ExponentialConjugationLaw
      (dynkinProduct a (basisBracket (b r))) (basisBracket (b r)))
    (k y : ℝ → Fin n → ℝ)
    {C A B α β : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hbound : ∀ᶠ r : ℝ in atTop, ‖basisBracket (b r)‖ ≤ C)
    (hgap : (m : ℝ) * α < β)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hksize : ∀ᶠ r : ℝ in atTop, ‖k r‖ ≤ A * Real.exp ((α + ε r) * r))
    (hysize : ∀ᶠ r : ℝ in atTop, ‖y r‖ ≤ B * Real.exp ((-β + ε r) * r)) :
    Tendsto (fun r => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) (k r) (y r)) (-(k r))) atTop (𝓝 0) := by
  let N : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fun r => basisBracket (b r) (k r)
  have hnil : ∀ r, (N r) ^ (m + 1) = 0 :=
    fun r => basisBracket_pow_eq_zero (b r) hk (k r)
  have hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ (C * A) * Real.exp ((α + ε r) * r) := by
    filter_upwards [hbound, hksize] with r hbr hr
    calc
      ‖N r‖ ≤ ‖basisBracket (b r)‖ * ‖k r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (A * Real.exp ((α + ε r) * r)) :=
        mul_le_mul hbr hr (norm_nonneg _) hC
      _ = _ := by ring
  have ht := nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    N y hnil (mul_nonneg hC hA) hB hα hgap ε hε hN hysize
  apply ht.congr
  intro r
  have h := hconj r (k r) (y r) 1
  simpa only [one_smul] using h.symm

end PolycyclicRecognition

end

end OAI
