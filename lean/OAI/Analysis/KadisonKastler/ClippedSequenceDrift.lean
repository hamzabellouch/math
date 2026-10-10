import OAI.Analysis.KadisonKastler.BoundedSequence
import OAI.Analysis.KadisonKastler.ClippedCoefficients

namespace OAI

/-! # Restoring the coordinate coefficient drift

The quotient norm estimate makes the discarded spectral tails strongly
zero. This applies to both fixed vectors and vectors moved by a bounded
unitary sequence. The latter restoration retains exactly the commutator
of that unitary, independently of the number of coefficients.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B Q H W : Type*} [CStarAlgebra B] [CStarAlgebra Q]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder Q] [StarOrderedRing Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype W]
  {τ : FaithfulTracialState B} {l : Filter ℕ}
  {π : BoundedSequence B →⋆ₐ[ℂ] Q} {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

local instance driftOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance driftOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The discarded column is contractive whenever the original one is. -/
theorem represented_discarded_column_contract
    (K : W → B) (β : W → ℝ) (hβ : ∀ w, 0 < β w)
    (hK : ∀ z : H, ‖WithLp.toLp 2 (fun w => ρ (K w) z)‖ ≤ ‖z‖) (z : H) :
    ‖WithLp.toLp 2 (fun w => ρ (K w - spectralClip (β w) (K w)) z)‖ ≤ ‖z‖ := by
  apply column_contract_of_star_mul_self_le (fun w => ρ (K w)) _ _ hK
  intro w
  have he := OrderHomClass.mono ρ
    (spectralClip_discard_star_mul_self_le (hβ w) (K w))
  simpa only [map_mul, map_star] using he

/-- Restore all finitely many clipped coefficients on a fixed vector. -/
theorem IsTraceQuotient.eventually_coefficient_drift
    (hπ : IsTraceQuotient τ l π) (hρ : TraceStrongContinuous τ ρ)
    (K : W → BoundedSequence B) (β : W → ℝ) (hβ : ∀ w, 0 < β w)
    (hbound : ∀ w, ‖π (K w)‖ ≤ β w)
    (T : H →L[ℂ] H) (z : H) {C : ℝ}
    (hclip : ∀ j, ‖WithLp.toLp 2 (fun w =>
      (T * ρ (spectralClip (β w) (K w j)) -
        ρ (spectralClip (β w) (K w j)) * T) z)‖ ≤ C) :
    ∀ ε > 0, ∀ᶠ j in l,
      ‖WithLp.toLp 2 (fun w => (T * ρ (K w j) - ρ (K w j) * T) z)‖ ≤ C + ε := by
  let E := fun j w => ρ (K w j - spectralClip (β w) (K w j))
  apply eventually_column_restored_drift_le l T
    (fun j w => ρ (K w j))
    (fun j w => ρ (spectralClip (β w) (K w j))) E
  · intro j w
    dsimp [E]
    rw [map_sub]
    abel
  · exact hclip
  · apply tendsto_column_norm_zero
    intro w
    simpa only [E, norm_zero] using
      (hπ.spectralDiscard_strong_zero hρ (hβ w) (K w) (hbound w) z).norm
  · apply tendsto_column_norm_zero
    intro w
    simpa only [E, norm_zero] using
      (hπ.spectralDiscard_strong_zero hρ (hβ w) (K w) (hbound w) (T z)).norm

/-- The moving-vector version costs only the given coordinate
commutator bound in addition to the clipped drift. -/
theorem IsTraceQuotient.eventually_moving_coefficient_drift
    (hπ : IsTraceQuotient τ l π) (hρ : TraceStrongContinuous τ ρ)
    (K : W → BoundedSequence B) (β : W → ℝ) (hβ : ∀ w, 0 < β w)
    (hbound : ∀ w, ‖π (K w)‖ ≤ β w)
    (hK : ∀ j z, ‖WithLp.toLp 2 (fun w => ρ (K w j) z)‖ ≤ ‖z‖)
    (s : BoundedSequence B) (T : H →L[ℂ] H) (y : H) {C D : ℝ}
    (hclip : ∀ j, ‖WithLp.toLp 2 (fun w =>
      (T * ρ (spectralClip (β w) (K w j)) -
        ρ (spectralClip (β w) (K w j)) * T) (ρ (s j) y))‖ ≤ C)
    (hcomm : ∀ j, ‖(T * ρ (s j) - ρ (s j) * T) y‖ ≤ D) :
    ∀ ε > 0, ∀ᶠ j in l,
      ‖WithLp.toLp 2 (fun w =>
        (T * ρ (K w j) - ρ (K w j) * T) (ρ (s j) y))‖ ≤ C + D + ε := by
  let E := fun j w => ρ (K w j - spectralClip (β w) (K w j))
  apply eventually_column_restored_moving_drift_le l T (fun j => ρ (s j))
    (fun j w => ρ (K w j))
    (fun j w => ρ (spectralClip (β w) (K w j))) E
  · intro j w
    dsimp [E]
    rw [map_sub]
    abel
  · intro j z
    exact represented_discarded_column_contract (fun w => K w j) β hβ (hK j) z
  · exact hclip
  · exact hcomm
  · apply tendsto_column_norm_zero
    intro w
    simpa only [E, norm_zero] using
      (hπ.spectralDiscard_mul_strong_zero hρ (hβ w) (K w) s (hbound w) y).norm
  · apply tendsto_column_norm_zero
    intro w
    simpa only [E, norm_zero] using
      (hπ.spectralDiscard_mul_strong_zero hρ (hβ w) (K w) s (hbound w) (T y)).norm

end

end KadisonKastler

end OAI
