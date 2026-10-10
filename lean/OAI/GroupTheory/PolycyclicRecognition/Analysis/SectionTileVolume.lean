import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialOperations

namespace OAI

/-! # The quotient trace in the per-tile volume exponent -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise

/-- A vanishing error in the exponent contributes a subexponential factor. -/
theorem subexponential_exp_error {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    HasSubexponentialUpperBound (fun r => Real.exp (ε r * r)) := by
  intro η hη
  filter_upwards [hε.eventually (eventually_lt_nhds hη), eventually_ge_atTop (0 : ℝ)]
    with r he hr
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he.le hr)

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsMulLeftInvariant]

omit [SFinite μQ] in
/-- The ideal exponent and the exact quotient multiplier combine to
`P - ell`. Arbitrary translated quotient locations are allowed. -/
theorem section_tile_volume_exponent
    (E : ℝ → Set N) (T : ℝ → Set Q) (B : ℝ → Set π.ker)
    (q₀ : ℝ → Q) (α : ℝ → Q ≃ Q)
    (P ell : ℝ) (ε U V : ℝ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hU : HasSubexponentialUpperBound U) (hV : HasSubexponentialUpperBound V)
    (hU0 : ∀ r, 0 ≤ U r) (hV0 : ∀ r, 0 ≤ V r)
    (hT : ∀ r, μQ (T r) ≠ ⊤) (hB : ∀ r, μI (B r) ≠ ⊤)
    (hα : ∀ r, μQ (α r '' T r) =
      ENNReal.ofReal (Real.exp (-ell * r + ε r * r)) * μQ (T r))
    (hTB : ∀ r, (μQ (T r)).toReal ≤ U r)
    (hIB : ∀ r, (μI (B r)).toReal ≤ V r * Real.exp (P * r))
    (hE : ∀ r, ∀ n ∈ E r, π n ∈ q₀ r • (α r '' T r) ∧
      quotientSectionResidual π s hs n ∈ B r) :
    ∃ L : ℝ → ℝ, HasSubexponentialUpperBound L ∧
      ∀ r, ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm
        (μQ.prod μI)) (E r)).toReal ≤ L r * Real.exp ((P - ell) * r) := by
  let L := fun r => U r * V r * Real.exp (ε r * r)
  have hL : HasSubexponentialUpperBound L :=
    (hU.mul hV (Eventually.of_forall hU0)).mul (subexponential_exp_error hε)
      (Eventually.of_forall (fun r => mul_nonneg (hU0 r) (hV0 r)))
  refine ⟨L, hL, ?_⟩
  intro r
  have hv := quotientSection_translated_real_volume_le π hπ s hs μQ μI
    (E r) (T r) (B r) (q₀ r) (α r) (-ell * r + ε r * r) (hα r) (hT r) (hB r) (hE r)
  calc
    _ ≤ Real.exp (-ell * r + ε r * r) * (μQ (T r)).toReal * (μI (B r)).toReal := hv
    _ ≤ Real.exp (-ell * r + ε r * r) * U r * (V r * Real.exp (P * r)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hTB r) (Real.exp_nonneg _))
        (hIB r) ENNReal.toReal_nonneg (mul_nonneg (Real.exp_nonneg _) (hU0 r))
    _ = L r * Real.exp ((P - ell) * r) := by
      dsimp only [L]
      rw [Real.exp_add]
      have hexp : Real.exp (-ell * r) * Real.exp (P * r) =
          Real.exp ((P - ell) * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = U r * V r * Real.exp (ε r * r) *
            (Real.exp (-ell * r) * Real.exp (P * r)) := by ring
        _ = _ := by rw [hexp]

end PolycyclicRecognition

end

end OAI
