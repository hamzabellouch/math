import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceQuotientVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSubsetVolume

namespace OAI

/-! # Weighted ideal-box volumes in a chosen Haar normalization -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The basis rescaling contributes exactly the sum of its coordinate
weights to the exponential volume rate. -/
theorem det_exponentialRescaleBasis {n : ℕ} (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ) (r : ℝ) :
    (b.toMatrix (exponentialRescaleBasis b cost r)).det = Real.exp (r * ∑ j, cost j) := by
  have hm : b.toMatrix (exponentialRescaleBasis b cost r) =
      Matrix.of (fun i j => Real.exp (r * cost j) * b.toMatrix b i j) := by
    ext i j
    simp only [Basis.toMatrix_apply, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Matrix.of_apply]
  rw [hm, Matrix.det_mul_row, ← Real.exp_sum]
  simp only [Basis.toMatrix_self, Matrix.det_one, mul_one]
  rw [Finset.mul_sum]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The same Haar normalization can be used for section coordinates and
weighted ideal boxes. The constant is fixed for all scales and radii. -/
theorem haar_model_weighted_box_volume
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ r R : ℝ, 0 ≤ R →
      μ (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) R) =
        (c : ℝ≥0∞) * ENNReal.ofReal (Real.exp (r * ∑ j, cost j)) *
          ENNReal.ofReal (2 * R) ^ n := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)
  let ν := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  have hν : ν.IsHaarMeasure := by
    have he : ((Exp ∘ e) ∘ b.equivFun.symm) = Exp ∘ (b.map e.toLinearEquiv).equivFun.symm := by
      funext z
      rw [Basis.map_equivFun]
      rfl
    dsimp only [ν]
    rw [he]
    exact hhaar n _
  let _ : ν.IsHaarMeasure := hν
  let coordinates := (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let _ : LocallyCompactSpace G := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let _ : SecondCountableTopology G := coordinates.symm.secondCountableTopology
  refine ⟨Measure.haarScalarFactor μ ν, Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν, ?_⟩
  intro r R hR
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  rw [Measure.smul_apply]
  have hvol : ν (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) R) =
      ENNReal.ofReal (Real.exp (r * ∑ j, cost j)) * ENNReal.ofReal (2 * R) ^ n := by
    rw [exponentialCoordinateBox_eq_cube_image _ _ R hR]
    rw [exponential_basis_subset_measure e Exp chart hchart b,
      det_exponentialRescaleBasis, abs_of_pos (Real.exp_pos _), Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hvol]
  exact mul_assoc _ _ _ |>.symm

/-- Unit boxes have a fixed strictly positive volume coefficient at every
scale. This is the lower exponential rate needed for the source probes. -/
theorem haar_model_weighted_unit_volume
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ v : ℝ, 0 < v ∧ ∀ r : ℝ,
      μ (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) 1) ≠ 0 ∧
      μ (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) 1) ≠ ⊤ ∧
      (μ (exponentialCoordinateBox (Exp ∘ e) (exponentialRescaleBasis b cost r) 1)).toReal =
        v * Real.exp (r * ∑ j, cost j) := by
  obtain ⟨c, hc, hvol⟩ := haar_model_weighted_box_volume haar Exp hExp e hnil b cost μ
  refine ⟨(c : ℝ) * 2 ^ n, mul_pos hc (pow_pos (by norm_num) _), ?_⟩
  intro r
  rw [hvol r 1 zero_le_one]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have he0 : ENNReal.ofReal (Real.exp (r * ∑ j, cost j)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  refine ⟨mul_ne_zero (mul_ne_zero hc0 he0) (by norm_num),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), ?_⟩
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_pow]
  norm_num only [mul_one, ENNReal.toReal_ofReal]
  ring

/-- Only the sum of the ideal widths contributes to the exponential rate;
the radius loss has a common subexponential volume bound. -/
theorem haar_model_sequence_weighted_boxes
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (μ : Measure G) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ j, 0 ≤ R j) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ j, 0 ≤ V j) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ j, μ (exponentialCoordinateBox (Exp ∘ e)
        (exponentialRescaleBasis b cost (scale j)) (R j)) ≠ ⊤ ∧
        (μ (exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis b cost (scale j)) (R j))).toReal =
            V j * Real.exp ((∑ k, cost k) * scale j) := by
  obtain ⟨c, _, hvol⟩ := haar_model_weighted_box_volume haar Exp hExp e hnil b cost μ
  let V := fun j => (c : ℝ) * (2 * R j) ^ n
  have htwo := (sequence_subexponential_upper_const hs 2).mul hR
    (Eventually.of_forall (fun _ => by norm_num))
  have hp := htwo.pow hs (Eventually.of_forall (fun j => mul_nonneg (by norm_num) (hR0 j))) n
  have hV := (sequence_subexponential_upper_const hs (c : ℝ)).mul hp
    (Eventually.of_forall (fun _ => c.coe_nonneg))
  refine ⟨V, fun j => mul_nonneg c.coe_nonneg (pow_nonneg (mul_nonneg (by norm_num) (hR0 j)) _), hV, ?_⟩
  intro j
  rw [hvol _ _ (hR0 j)]
  constructor
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hR0 j))]
    dsimp only [V]
    rw [mul_comm (∑ k, cost k) (scale j)]
    ring

end PolycyclicRecognition

end

end OAI
