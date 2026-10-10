import OAI.MeasureTheory.Falconer.Slicing.HyperplaneSlice
import OAI.MeasureTheory.Falconer.Geometry.ChartCoordinates
import OAI.MeasureTheory.Falconer.Geometry.EuclideanTrace

namespace OAI

/-! A measurable majorant for the actual Fourier energy on each hyperplane. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal Topology

noncomputable def hyperplaneFourierWeight {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (ξ : Space (n+1)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖sourceFourier μ ξ‖^2 * ‖ξ‖^(s-n))

theorem hyperplaneFourierWeight_continuous {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs : (n : ℝ) < s) :
    Continuous (hyperplaneFourierWeight μ s) := by
  apply ENNReal.continuous_ofReal.comp
  apply Continuous.mul
  · unfold sourceFourier
    fun_prop
  · exact continuous_norm.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hs.le))

noncomputable def hyperplaneFourierEnergy {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (w : Sphere (n+1)) : ℝ≥0∞ :=
  ∫⁻ ξ : Space n, hyperplaneFourierWeight μ s (hyperplaneSliceEmbedding w ξ)

noncomputable def hyperplaneEnergyMajorant {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (w : Sphere (n+1)) : ℝ≥0∞ :=
  slabSliceMajorant (hyperplaneFourierWeight μ s) w

theorem hyperplaneEnergyMajorant_measurable {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs : (n : ℝ) < s) :
    Measurable (hyperplaneEnergyMajorant μ s) :=
  slabSliceMajorant_measurable (hyperplaneFourierWeight_continuous μ hs).measurable

theorem hyperplaneFourierEnergy_le_majorant {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs : (n : ℝ) < s) (w : Sphere (n+1)) :
    hyperplaneFourierEnergy μ s w ≤ hyperplaneEnergyMajorant μ s w :=
  hyperplane_slice_le_majorant (hyperplaneFourierWeight_continuous μ hs) w

theorem hyperplaneSliceEmbedding_norm {n : ℕ} (w : Sphere (n+1)) (ξ : Space n) :
    ‖hyperplaneSliceEmbedding w ξ‖ = ‖ξ‖ := by
  rw [hyperplaneSliceEmbedding, LinearIsometryEquiv.norm_map]
  have h := coordinateJoin_norm_sq ξ 0
  nlinarith [norm_nonneg (coordinateJoin ξ 0), norm_nonneg ξ]

theorem hyperplaneFourierEnergy_formula {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (w : Sphere (n+1)) :
    hyperplaneFourierEnergy μ s w = ∫⁻ ξ : Space n,
      ENNReal.ofReal (‖sourceFourier μ (hyperplaneSliceEmbedding w ξ)‖^2 * ‖ξ‖^(s-n)) := by
  simp only [hyperplaneFourierEnergy, hyperplaneFourierWeight, hyperplaneSliceEmbedding_norm]

theorem hyperplaneFourierWeight_ambient {n : ℕ} (μ : Measure (Space (n+1))) (s : ℝ) :
    (∫⁻ ξ : Space (n+1), hyperplaneFourierWeight μ s ξ * (ENNReal.ofReal ‖ξ‖)⁻¹) =
      ∫⁻ ξ : Space (n+1), ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(s-(n+1 : ℕ))) := by
  apply lintegral_congr_ae
  have hne : ∀ᵐ ξ : Space (n+1) ∂volume, ξ ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hne] with ξ hξ
  have hn := norm_pos_iff.mpr hξ
  rw [hyperplaneFourierWeight, ← ENNReal.ofReal_inv_of_pos hn,
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hn.le _)),
    ← ENNReal.ofReal_mul (sq_nonneg _), mul_assoc,
    ← Real.rpow_neg_one, ← Real.rpow_add hn]
  congr 3
  push_cast
  ring

theorem hyperplaneEnergyMajorant_integral_bound {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s)
    (hsn : s < n+1) :
    ENNReal.ofReal (sourceEnergyConstant (n+1) s) *
      (∫⁻ w : Sphere (n+1), hyperplaneEnergyMajorant μ s w ∂sphereMeasure (n+1)) ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2) * rieszEnergyOn μ s := by
  have h := mul_le_mul_right (slabSliceMajorant_integral_bound n
    (hyperplaneFourierWeight_continuous μ hs).measurable)
      (ENNReal.ofReal (sourceEnergyConstant (n+1) s))
  rw [hyperplaneFourierWeight_ambient] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  have he := source_fourier_energy_identity μ hs0 (by simpa [Space] using hsn)
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at he
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one]
  convert h using 1 <;> ac_rfl

theorem hyperplaneEnergyMajorant_integrable {n : ℕ} (μ : Measure (Space (n+1)))
    [IsFiniteMeasure μ] {s : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s)
    (hsn : s < n+1) (hμ : rieszEnergyOn μ s < ∞) :
    (∫⁻ w : Sphere (n+1), hyperplaneEnergyMajorant μ s w ∂sphereMeasure (n+1)) < ∞ := by
  have h := (hyperplaneEnergyMajorant_integral_bound μ hs0 hs hsn).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ)
  have hc : ENNReal.ofReal (sourceEnergyConstant (n+1) s) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sourceEnergyConstant_pos hs0 hsn)).ne'
  exact ENNReal.lt_top_of_mul_ne_top_right h.ne hc

end Falconer

end OAI
