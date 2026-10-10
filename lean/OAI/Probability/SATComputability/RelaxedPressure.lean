import OAI.Probability.SATComputability.SignLaw
import OAI.Probability.SATComputability.VariableDeletion

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable def relaxedPartition {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℝ :=
  ∑ s : Fin n → Bool, Real.exp (-β * relaxedViolations s indices signs)

noncomputable def relaxedLogPartition {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℝ :=
  Real.log (relaxedPartition β indices signs)

theorem satModel_logWeight {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool)
    (s : Fin n → Bool) :
    logWeight (fun j => satSample β (signs j)) (fun _ => 0) indices s =
      -β * relaxedViolations s indices signs := by
  classical
  have h (j : Fin m) : satInteraction β (signs j) (fun l => s (indices j l)) =
      -β * (if ¬relaxedClauseSatisfied s (indices j) (signs j) then 1 else 0) := by
    simp [satInteraction, relaxedClauseSatisfied, not_exists]
  simp only [logWeight, satSample, zero_mul, Finset.sum_const_zero, add_zero, h,
    ← Finset.mul_sum]
  congr 1
  simp only [relaxedViolations, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, ite_not, apply_ite, Nat.cast_one, Nat.cast_zero]

theorem satModel_logPartition {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    DilutedSpinGlass.logPartition (fun j => satSample β (signs j)) (fun _ => 0) indices =
      relaxedLogPartition β indices signs := by
  simp only [DilutedSpinGlass.logPartition, satModel_logWeight,
    relaxedLogPartition, relaxedPartition]

theorem zeroField_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∫ h, f h ∂Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ))) =
      f (fun _ => 0) := by
  have h : (fun h : Fin n → ℝ => fun i => h i) =ᵐ[
      Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ))] (fun _ => fun _ => 0) :=
    Measure.ae_eq_pi (fun _ => ae_eq_dirac (fun x : ℝ => x))
  calc
    _ = ∫ _h, f (fun _ => 0) ∂Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [h] with h hh
      exact congrArg f hh
    _ = _ := by simp

theorem signLaw_pi_integral (m : ℕ) (f : (Fin m → Fin 3 → Bool) → ℝ) :
    (∫ J, f J ∂Measure.pi (fun _ : Fin m => signLaw.toMeasure)) =
      (∑ J, f J) / Fintype.card (Fin m → Fin 3 → Bool) := by
  have he : Measure.pi (fun _ : Fin m => signLaw.toMeasure) =
      (PMF.uniformOfFintype (Fin m → Fin 3 → Bool)).toMeasure := by
    apply Measure.ext_of_singleton
    intro J
    simp [Measure.pi_singleton, signLaw, Nat.cast_pow,
      ENNReal.inv_pow]
  rw [he, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv]
  ring

theorem disorder_pi_integral (a : ℝ≥0) (β : ℝ) (m : ℕ)
    (f : (Fin m → InteractionSample 3) → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂Measure.pi (fun _ : Fin m => (satModel a β).disorder.toMeasure)) =
      (∑ J : Fin m → Fin 3 → Bool, f (fun j => satSample β (J j))) /
        Fintype.card (Fin m → Fin 3 → Bool) := by
  change (∫ z, f z ∂Measure.pi (fun _ : Fin m =>
    Measure.map (satSample β) signLaw.toMeasure)) = _
  rw [← Measure.pi_map_pi (fun _ : Fin m =>
    (measurable_of_countable (satSample β)).aemeasurable)]
  rw [integral_map (measurable_of_countable (fun J : Fin m → Fin 3 → Bool =>
    fun j => satSample β (J j))).aemeasurable
    hf.aestronglyMeasurable]
  exact signLaw_pi_integral m _

noncomputable def relaxedFixedLogPartition (n m : ℕ) (β : ℝ) : ℝ :=
  (∑ J : Fin m → Fin 3 → Bool,
    (∑ indices : Fin m → Fin 3 → Fin n, relaxedLogPartition β indices J) /
      Fintype.card (Fin m → Fin 3 → Fin n)) /
    Fintype.card (Fin m → Fin 3 → Bool)

noncomputable def relaxedPoissonPressure (a : ℝ≥0) (β : ℝ) (n : ℕ) : ℝ :=
  (∫ m : ℕ, relaxedFixedLogPartition n m β ∂poissonMeasure (a * n)) / n

theorem satModel_pressure (a : ℝ≥0) (β : ℝ) (n : ℕ) :
    pressure (satModel a β) n = relaxedPoissonPressure a β n := by
  unfold pressure relaxedPoissonPressure
  congr 1
  apply integral_congr_ae
  filter_upwards [] with m
  change (∫ z : Fin m → InteractionSample 3,
      ∫ h : Fin n → ℝ,
        (∑ indices : Fin m → Fin 3 → Fin n, DilutedSpinGlass.logPartition z h indices) /
          Fintype.card (Fin m → Fin 3 → Fin n)
        ∂Measure.pi (fun _ : Fin n => Measure.dirac (0 : ℝ))
      ∂Measure.pi (fun _ : Fin m => (satModel a β).disorder.toMeasure)) = _
  simp_rw [zeroField_integral]
  rw [disorder_pi_integral a β m _ (by
    unfold DilutedSpinGlass.logPartition logWeight
    fun_prop)]
  simp only [satModel_logPartition, relaxedFixedLogPartition]

end FixedClauseThreshold.Computability

end OAI
