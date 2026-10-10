import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionTileVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The per-tile Haar exponent along the sampled profile scales -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology Pointwise

theorem sequence_subexponential_exp_error
    {scale ε : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (hε : Tendsto ε atTop (𝓝 0)) :
    HasSubexponentialUpperBoundSeq scale (fun n => Real.exp (ε n * scale n)) := by
  intro η hη
  filter_upwards [hε.eventually (eventually_lt_nhds hη),
    hs.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hs
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn.le hs)

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsMulLeftInvariant]

omit [SFinite μQ] in
/-- Arbitrary translations of the quotient do not alter its Haar multiplier.
The ideal and quotient constraints give the exact P-minus-trace exponent. -/
theorem sequence_section_tile_volume_exponent
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (E : ℕ → Set N) (T : ℕ → Set Q) (B : ℕ → Set π.ker)
    (q₀ : ℕ → Q) (α : ℕ → Q ≃ Q)
    (P ell : ℝ) (ε U V : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hB : ∀ n, μI (B n) ≠ ⊤)
    (hα : ∀ n, μQ (α n '' T n) =
      ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) * μQ (T n))
    (hTB : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIB : ∀ n, (μI (B n)).toReal ≤ V n * Real.exp (P * scale n))
    (hE : ∀ n, ∀ x ∈ E n, π x ∈ q₀ n • (α n '' T n) ∧
      quotientSectionResidual π s hs x ∈ B n) :
    ∃ L : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale L ∧ (∀ n, 0 ≤ L n) ∧
      ∀ n, ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm
        (μQ.prod μI)) (E n)).toReal ≤ L n * Real.exp ((P - ell) * scale n) := by
  let L := fun n => U n * V n * Real.exp (ε n * scale n)
  have hL : HasSubexponentialUpperBoundSeq scale L :=
    (hU.mul hV (Eventually.of_forall hU0)).mul (sequence_subexponential_exp_error hscale hε)
      (Eventually.of_forall (fun n => mul_nonneg (hU0 n) (hV0 n)))
  refine ⟨L, hL, fun n => mul_nonneg (mul_nonneg (hU0 n) (hV0 n)) (Real.exp_pos _).le, ?_⟩
  intro n
  have hv := quotientSection_translated_real_volume_le π hπ s hs μQ μI
    (E n) (T n) (B n) (q₀ n) (α n) (-ell * scale n + ε n * scale n)
    (hα n) (hT n) (hB n) (hE n)
  calc
    _ ≤ Real.exp (-ell * scale n + ε n * scale n) *
        (μQ (T n)).toReal * (μI (B n)).toReal := hv
    _ ≤ Real.exp (-ell * scale n + ε n * scale n) * U n *
        (V n * Real.exp (P * scale n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hTB n) (Real.exp_nonneg _))
        (hIB n) ENNReal.toReal_nonneg (mul_nonneg (Real.exp_nonneg _) (hU0 n))
    _ = L n * Real.exp ((P - ell) * scale n) := by
      dsimp only [L]
      rw [Real.exp_add]
      have he : Real.exp (-ell * scale n) * Real.exp (P * scale n) =
          Real.exp ((P - ell) * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = U n * V n * Real.exp (ε n * scale n) *
            (Real.exp (-ell * scale n) * Real.exp (P * scale n)) := by ring
        _ = _ := by rw [he]

omit [SFinite μQ] in
/-- All tiles share one subexponential loss even though their quotient
translations and automorphisms vary independently. This also proves the
finiteness needed by the separated-cell packing inequality. -/
theorem sequence_section_tile_family_volume_exponent
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {J : ℕ → Type*} (E : ∀ n, J n → Set N) (T : ℕ → Set Q) (B : ℕ → Set π.ker)
    (q₀ : ∀ n, J n → Q) (α : ∀ n, J n → Q ≃ Q)
    (P ell : ℝ) (ε U V : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hU : HasSubexponentialUpperBoundSeq scale U)
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hU0 : ∀ n, 0 ≤ U n) (hV0 : ∀ n, 0 ≤ V n)
    (hT : ∀ n, μQ (T n) ≠ ⊤) (hB : ∀ n, μI (B n) ≠ ⊤)
    (hα : ∀ n j, μQ (α n j '' T n) ≤
      ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) * μQ (T n))
    (hTB : ∀ n, (μQ (T n)).toReal ≤ U n)
    (hIB : ∀ n, (μI (B n)).toReal ≤ V n * Real.exp (P * scale n))
    (hE : ∀ n j, ∀ x ∈ E n j, π x ∈ q₀ n j • (α n j '' T n) ∧
      quotientSectionResidual π s hs x ∈ B n) :
    ∃ loss : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale loss ∧
      (∀ n, 0 ≤ loss n) ∧ ∀ n j,
        (Measure.map (quotientSectionHomeomorph π hπ s hs).symm
          (μQ.prod μI)) (E n j) ≠ ⊤ ∧
        ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm
          (μQ.prod μI)) (E n j)).toReal ≤
          loss n * Real.exp ((P - ell) * scale n) := by
  let loss := fun n => U n * V n * Real.exp (ε n * scale n)
  have hloss : HasSubexponentialUpperBoundSeq scale loss :=
    (hU.mul hV (Eventually.of_forall hU0)).mul
      (sequence_subexponential_exp_error hscale hε)
      (Eventually.of_forall (fun n => mul_nonneg (hU0 n) (hV0 n)))
  refine ⟨loss, hloss,
    fun n => mul_nonneg (mul_nonneg (hU0 n) (hV0 n)) (Real.exp_pos _).le, ?_⟩
  intro n j
  have hfinite : ENNReal.ofReal (Real.exp (-ell * scale n + ε n * scale n)) *
      μQ (T n) * μI (B n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hT n)) (hB n)
  have hbound := quotientSection_measure_le π hπ s hs μQ μI (E n j)
    (q₀ n j • (α n j '' T n)) (B n) (hE n j)
  rw [measure_smul] at hbound
  have hbound' := hbound.trans (mul_le_mul' (hα n j) le_rfl)
  refine ⟨ne_top_of_le_ne_top hfinite hbound', ?_⟩
  have hv : ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm
      (μQ.prod μI)) (E n j)).toReal ≤
      Real.exp (-ell * scale n + ε n * scale n) *
        (μQ (T n)).toReal * (μI (B n)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono hfinite hbound'
  calc
    _ ≤ Real.exp (-ell * scale n + ε n * scale n) *
        (μQ (T n)).toReal * (μI (B n)).toReal := hv
    _ ≤ Real.exp (-ell * scale n + ε n * scale n) * U n *
        (V n * Real.exp (P * scale n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hTB n) (Real.exp_nonneg _))
        (hIB n) ENNReal.toReal_nonneg (mul_nonneg (Real.exp_nonneg _) (hU0 n))
    _ = loss n * Real.exp ((P - ell) * scale n) := by
      dsimp only [loss]
      rw [Real.exp_add]
      have he : Real.exp (-ell * scale n) * Real.exp (P * scale n) =
          Real.exp ((P - ell) * scale n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = U n * V n * Real.exp (ε n * scale n) *
            (Real.exp (-ell * scale n) * Real.exp (P * scale n)) := by ring
        _ = _ := by rw [he]

end PolycyclicRecognition

end

end OAI
