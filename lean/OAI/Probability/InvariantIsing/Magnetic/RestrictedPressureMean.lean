import OAI.Probability.InvariantIsing.Cavity.ConsecutiveFieldPressure
import OAI.Probability.InvariantIsing.Cavity.ConsecutivePhysicalIncrement
import OAI.Probability.InvariantIsing.Pressure.GroundStateMean

namespace OAI

/-! Integrable physical constrained pressures and expectation comparison
with the full external-field pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma measurable_physicalRestrictedPressure {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (eig c : Fin N → ℝ) :
    Measurable (fun V : Orthogonal N => restrictedRotatedPressure S eig (matrixRotation V⁻¹) c) := by
  have hm := (measurable_restrictedRotatedPressure S eig c).comp
    ((measurable_cavityOrientationLift hN).comp measurable_inv)
  convert hm using 1
  funext V
  simp only [Function.comp_apply, restrictedRotatedPressure, cavityOrientationLift_energy]

lemma integrable_physicalRestrictedPressure {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig c : Fin N → ℝ) :
    Integrable (fun V => restrictedRotatedPressure S eig (matrixRotation V⁻¹) c) μ := by
  let B := (∑ i, |eig i|)*N/2+∑ i, |c i|
  have hb (V : Orthogonal N) (σ : Spin N) :
      |rotatedEnergy eig (matrixRotation V⁻¹) σ+fieldEnergy c σ| ≤ B := by
    have hq := abs_rotatedEnergy_le eig (matrixRotation V⁻¹) (∑ i, |eig i|)
      (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i)) σ
    have hf := abs_fieldEnergy_sub_le c 0 σ
    simp only [fieldEnergy, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at hf
    exact (abs_add_le _ _).trans (add_le_add hq hf)
  apply Integrable.of_bound (measurable_physicalRestrictedPressure hN S eig c).aestronglyMeasurable
    ((N : ℝ)⁻¹*(B+|restrictedSpinLog S (fun _ => 0)|))
  apply ae_of_all
  intro V
  rw [Real.norm_eq_abs, restrictedRotatedPressure, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  have hh := abs_restrictedSpinLog_sub_le S hS
    (fun σ => rotatedEnergy eig (matrixRotation V⁻¹) σ+fieldEnergy c σ) (fun _ => 0) B
    (fun σ _ => by simpa only [sub_zero] using hb V σ)
  have ha := abs_add_le
    (restrictedSpinLog S (fun σ => rotatedEnergy eig (matrixRotation V⁻¹) σ+fieldEnergy c σ)-
      restrictedSpinLog S (fun _ => 0)) (restrictedSpinLog S (fun _ => 0))
  rw [sub_add_cancel] at ha
  exact ha.trans (add_le_add hh le_rfl)

lemma mean_consecutive_field_pressure_lower {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (μ : Measure (Orthogonal (K*n))) [IsProbabilityMeasure μ]
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    (eig : Fin (K*n) → ℝ) :
    (∫ V, restrictedRotatedPressure (consecutiveBlockConstraint n K C) eig
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ)+M/n ≤
    ∫ V, rotatedPressure eig (matrixRotation V⁻¹) (consecutiveBlockField K b) ∂μ := by
  have hdim : 0 < K*n := Nat.mul_pos hK hn
  have hi := integrable_physicalRestrictedPressure hdim μ _ (consecutiveBlockConstraint_nonempty C hC)
    eig (fun _ => 0)
  have hf := integrable_physicalPressure hdim μ id measurable_id eig (consecutiveBlockField K b)
  have hh := integral_mono (hi.add (integrable_const (M/n))) hf
    (fun V => consecutive_field_pressure_lower hn hK C hC b M hM eig (matrixRotation V⁻¹))
  simp only [Pi.add_apply, id_eq] at hh
  simpa only [integral_add hi (integrable_const (M/n)), integral_const, probReal_univ, one_smul] using hh

end InvariantIsing

end

end OAI
