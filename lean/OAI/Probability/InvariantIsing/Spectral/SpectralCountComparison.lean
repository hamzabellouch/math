import OAI.Probability.InvariantIsing.Spectral.SpectralCountEndpoint
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! Pressure comparison from the fractions of changed axes in the two
endpoint eigenspaces. This is the analytic part of manuscript Lemma gen:counts. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_countPressure {N : ℕ} (eig c : Fin N → ℝ) :
    Measurable (fun U : SpecialOrthogonal N => rotatedPressure eig (specialRotation U) c) := by
  exact measurable_rotatedPressure eig c

lemma integrable_countPressure {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (eig c : Fin N → ℝ) (K : ℝ) (heig : ∀ i, |eig i| ≤ K) :
    Integrable (fun U => rotatedPressure eig (specialRotation U) c) μ := by
  apply (integrable_const (K / 2 + |noninteractingPressure c|)).mono'
    (measurable_countPressure eig c).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs]
  have hb := abs_pressure_sub_noninteracting_le hN eig c (specialRotation U) K heig
  have ha := abs_add_le (rotatedPressure eig (specialRotation U) c - noninteractingPressure c)
    (noninteractingPressure c)
  rw [sub_add_cancel] at ha
  exact ha.trans (add_le_add hb le_rfl)

lemma rotatedPressure_spectral_secant {N : ℕ} (eig kap c : Fin N → ℝ)
    (U : SpecialOrthogonal N) :
    (N : ℝ)⁻¹ * (1 / 2) * gibbsAverage (fun _ => 1) (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, (kap i - eig i) * spinCoordinate (specialToOrthogonal U) σ i ^ 2) ≤
      rotatedPressure kap (specialRotation U) c - rotatedPressure eig (specialRotation U) c ∧
    rotatedPressure kap (specialRotation U) c - rotatedPressure eig (specialRotation U) c ≤
      (N : ℝ)⁻¹ * (1 / 2) * gibbsAverage (fun _ => 1) (orbitHamiltonian kap c (specialToOrthogonal U))
        (fun σ => ∑ i, (kap i - eig i) * spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
  have h := log_finitePartition_secant_bounds GibbsReference_one
    (orbitHamiltonian eig c (specialToOrthogonal U)) (orbitHamiltonian kap c (specialToOrthogonal U))
  have hd (σ : Spin N) : orbitHamiltonian kap c (specialToOrthogonal U) σ - orbitHamiltonian eig c (specialToOrthogonal U) σ =
      (1 / 2 : ℝ) * ∑ i, (kap i - eig i) * spinCoordinate (specialToOrthogonal U) σ i ^ 2 := by
    simp only [orbitHamiltonian, add_sub_add_right_eq_sub, rotatedEnergy,
      sub_mul, Finset.sum_sub_distrib, spinCoordinate]
    ring
  have he : Real.log (finitePartition (fun _ : Spin N => 1) (orbitHamiltonian kap c (specialToOrthogonal U))) -
      Real.log (finitePartition (fun _ : Spin N => 1) (orbitHamiltonian eig c (specialToOrthogonal U))) =
      logPartition (orbitHamiltonian kap c (specialToOrthogonal U)) - logPartition (orbitHamiltonian eig c (specialToOrthogonal U)) := by
    simp only [logPartition_eq, finitePartition, one_mul]
    ring
  simp_rw [hd] at h
  rw [gibbsAverage_const_mul, gibbsAverage_const_mul, he] at h
  constructor
  · convert mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr (Nat.cast_nonneg N)) using 1 <;>
      simp only [rotatedPressure, mul_sub, mul_assoc]
    all_goals rfl
  · convert mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr (Nat.cast_nonneg N)) using 1 <;>
      simp only [rotatedPressure, mul_sub, mul_assoc]
    all_goals rfl

/-- Changing a fraction at most `r` of every endpoint eigenspace changes the
mean pressure by at most `L*r/2`, where every eigenvalue displacement is at most `L`. -/
theorem meanPressure_change_counts_le {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig kap c : Fin N → ℝ) (K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (hkap : ∀ i, |kap i| ≤ K)
    (label label' : Fin N → Fin m)
    (hl : Function.Surjective label) (hl' : Function.Surjective label')
    (lam : Fin m → ℝ) (he : ∀ i, eig i = lam (label i))
    (hk : ∀ i, kap i = lam (label' i))
    (changed : Finset (Fin N)) (hzero : ∀ i, i ∉ changed → kap i = eig i)
    (L r : ℝ) (hL : 0 ≤ L) (hdelta : ∀ i, |kap i - eig i| ≤ L)
    (hc : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ))
    (hc' : ∀ a, ((changed.filter fun i => label' i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label' i = a).card : ℝ)) :
    |(∫ U, rotatedPressure kap (specialRotation U) c ∂μ) -
      ∫ U, rotatedPressure eig (specialRotation U) c ∂μ| ≤ L * r / 2 := by
  let delta := fun i => kap i - eig i
  have hz : ∀ i, i ∉ changed → delta i = 0 := by
    intro i hi
    simp only [delta, hzero i hi, sub_self]
  have hAe := integrable_gibbsSpectralDirection μ GibbsReference_one eig c delta
  have hAk := integrable_gibbsSpectralDirection μ GibbsReference_one kap c delta
  have hPe := integrable_countPressure hN μ eig c K heig
  have hPk := integrable_countPressure hN μ kap c K hkap
  have hlo := integral_mono (hAe.const_mul ((N : ℝ)⁻¹ * (1 / 2))) (hPk.sub hPe)
    (fun U => (rotatedPressure_spectral_secant eig kap c U).1)
  have hup := integral_mono (hPk.sub hPe) (hAk.const_mul ((N : ℝ)⁻¹ * (1 / 2)))
    (fun U => (rotatedPressure_spectral_secant eig kap c U).2)
  have hsub : (∫ U, rotatedPressure kap (specialRotation U) c -
      rotatedPressure eig (specialRotation U) c ∂μ) =
      (∫ U, rotatedPressure kap (specialRotation U) c ∂μ) -
        ∫ U, rotatedPressure eig (specialRotation U) c ∂μ := integral_sub hPk hPe
  simp only [Pi.sub_apply] at hlo hup
  rw [integral_const_mul, hsub] at hlo
  rw [integral_const_mul, hsub] at hup
  have hbe := abs_integral_gibbsSpectralDirection_le μ GibbsReference_one eig c delta
    label hl lam he changed hz L r hL hdelta hc
  have hbk := abs_integral_gibbsSpectralDirection_le μ GibbsReference_one kap c delta
    label' hl' lam hk changed hz L r hL hdelta hc'
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn0 : 0 ≤ (N : ℝ)⁻¹ * (1 / 2) := by positivity
  have hbL := mul_le_mul_of_nonneg_left (abs_le.mp hbe).1 hn0
  have hbU := mul_le_mul_of_nonneg_left (abs_le.mp hbk).2 hn0
  have hs : (N : ℝ)⁻¹ * (1 / 2) * (L * r * N) = L * r / 2 := by field_simp
  have hs' : (N : ℝ)⁻¹ * (1 / 2) * -(L * r * N) = -(L * r / 2) := by
    rw [mul_neg, hs]
  rw [hs'] at hbL
  rw [hs] at hbU
  exact abs_le.mpr ⟨hbL.trans hlo, hup.trans hbU⟩

end InvariantIsing

end

end OAI
