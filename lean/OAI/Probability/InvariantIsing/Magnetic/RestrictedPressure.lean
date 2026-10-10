import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior
import OAI.Probability.InvariantIsing.Pressure.Concentration

namespace OAI

/-! Physical pressure on a fixed spin constraint, retaining its original
cube mass. The Haar Lipschitz constant is independent of the constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def restrictedRotatedPressure {N : ℕ} (S : Finset (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * restrictedSpinLog S (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)

lemma restrictedRotatedPressure_univ {N : ℕ} (eig : Fin N → ℝ)
    (U : Rotation N) (c : Fin N → ℝ) :
    restrictedRotatedPressure Finset.univ eig U c = rotatedPressure eig U c := by
  rw [restrictedRotatedPressure, restrictedSpinLog_univ]
  rfl

lemma restrictedRotatedPressure_le_full {N : ℕ} (S : Finset (Spin N))
    (hS : S.Nonempty) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) :
    restrictedRotatedPressure S eig U c ≤ rotatedPressure eig U c :=
  mul_le_mul_of_nonneg_left (restrictedSpinLog_le_full S hS _) (by positivity)

lemma restrictedRotatedPressure_eq_prior {N : ℕ} (S : Finset (Spin N))
    (hS : S.Nonempty) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) :
    restrictedRotatedPressure S eig U c =
      (N : ℝ)⁻¹ * finiteLogIntegral (restrictedSpinPrior S hS : Measure (Spin N))
        (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) +
      (N : ℝ)⁻¹ * (Real.log S.card - N * Real.log 2) := by
  rw [finiteLogIntegral_restrictedSpinPrior]
  unfold restrictedRotatedPressure
  ring

lemma abs_restrictedRotatedPressure_sub_field_le {N : ℕ} (S : Finset (Spin N))
    (hS : S.Nonempty) (eig : Fin N → ℝ) (U : Rotation N) (c d : Fin N → ℝ) :
    |restrictedRotatedPressure S eig U c - restrictedRotatedPressure S eig U d| ≤
      (N : ℝ)⁻¹ * ∑ i, |c i - d i| := by
  have he := abs_restrictedSpinLog_sub_le S hS
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy eig U σ + fieldEnergy d σ) (∑ i, |c i - d i|)
    (fun σ _ => by simpa only [add_sub_add_left_eq_sub] using abs_fieldEnergy_sub_le c d σ)
  simpa only [restrictedRotatedPressure, ← mul_sub, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)] using
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg N))

lemma abs_restrictedRotatedPressure_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (U V : SpecialOrthogonal N) (c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |restrictedRotatedPressure S eig (specialRotation U) c -
      restrictedRotatedPressure S eig (specialRotation V) c| ≤ K * frobeniusDistance U V := by
  have he := abs_restrictedSpinLog_sub_le S hS
    (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)
    (K * N * frobeniusDistance U V) (fun σ _ => by
      simpa only [add_sub_add_right_eq_sub] using
        abs_rotatedEnergy_sub_rotation_le eig U V K hK heig σ)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  calc
    _ = (N : ℝ)⁻¹ * |restrictedSpinLog S
        (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) -
        restrictedSpinLog S (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)| := by
      rw [restrictedRotatedPressure, restrictedRotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (K * N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp

lemma measurable_restrictedRotatedPressure {N : ℕ} (S : Finset (Spin N))
    (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N => restrictedRotatedPressure S eig (specialRotation U) c) := by
  have hE (σ : Spin N) : Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) := by
    exact ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul
        (eig i)).const_mul (1 / 2 : ℝ)).add_const _
  unfold restrictedRotatedPressure restrictedSpinLog
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).log.sub_const _).const_mul _

end InvariantIsing

end

end OAI
