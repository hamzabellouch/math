import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Quotient log boxes in the chosen Haar normalization

The quotient Jacobian and the packing argument use the same Haar measure.
Uniqueness of Haar measure transfers the exponential cube formula to that
normalization, including along an arbitrary sequence of profile scales.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology ENNReal NNReal

variable {E Q L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [SimplyConnectedSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] [LieRing L] [LieAlgebra ℝ L]

/-- The logarithmic cube formula for any actual Lie-algebra model and any
Haar normalization. The constant is independent of the cube radius. -/
theorem haar_model_cube_volume
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (μ : Measure Q) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ R : ℝ, 0 ≤ R →
      μ (exponentialCoordinateBox (Exp ∘ e) b R) =
        (c : ℝ≥0∞) * ENNReal.ofReal (2 * R) ^ n := by
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨chart, ν, _, hν, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp
    (e.nilpotent_iff_equiv_nilpotent.mp hnil) (b.map e.toLinearEquiv)
  let coordinates : (Fin n → ℝ) ≃ₜ Q :=
    (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let : LocallyCompactSpace Q := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology Q := coordinates.symm.secondCountableTopology
  have : ν.IsHaarMeasure := hν
  have hbox (R : ℝ) : exponentialCoordinateBox (Exp ∘ e) b R =
      exponentialCoordinateBox Exp (b.map e.toLinearEquiv) R := by
    ext q
    constructor
    · rintro ⟨v, rfl, hv⟩
      refine ⟨e v, rfl, ?_⟩
      change ‖(b.map e.toLinearEquiv).equivFun (e.toLinearEquiv v)‖ ≤ R
      simpa only [Basis.map_equivFun, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply] using hv
    · rintro ⟨v, rfl, hv⟩
      refine ⟨e.symm v, by simp, ?_⟩
      change ‖b.equivFun (e.toLinearEquiv.symm v)‖ ≤ R
      simpa only [Basis.map_equivFun, LinearEquiv.trans_apply] using hv
  refine ⟨Measure.haarScalarFactor μ ν, Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν,
    ?_⟩
  intro R hR
  rw [hbox]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  rw [Measure.smul_apply, hvol R hR]
  rfl

/-- Subexponential radii have finite, subexponential Haar volume in the
normalization already used for the quotient action. -/
theorem haar_model_sequence_boxes
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (μ : Measure Q) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ j, 0 ≤ R j) (hR : HasSubexponentialUpperBoundSeq scale R) :
    (∀ j, μ (exponentialCoordinateBox (Exp ∘ e) b (R j)) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun j =>
        (μ (exponentialCoordinateBox (Exp ∘ e) b (R j))).toReal) := by
  obtain ⟨c, _, hvol⟩ := haar_model_cube_volume haar Exp hExp e hnil b μ
  have htwo := (sequence_subexponential_upper_const hs 2).mul hR
    (Eventually.of_forall (fun _ => by norm_num))
  have hp := htwo.pow hs
    (Eventually.of_forall (fun j => mul_nonneg (by norm_num) (hR0 j))) n
  have hc := (sequence_subexponential_upper_const hs (c : ℝ)).mul hp
    (Eventually.of_forall (fun _ => c.coe_nonneg))
  constructor
  · intro j
    rw [hvol _ (hR0 j)]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · intro ε hε
    filter_upwards [hc ε hε] with j hj
    rw [hvol _ (hR0 j), ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal
        (mul_nonneg (by norm_num) (hR0 j))]
    exact hj

end PolycyclicRecognition

end

end OAI
