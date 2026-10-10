import OAI.Probability.InvariantIsing.Arrays.NSpinCascade
import OAI.Probability.InvariantIsing.Pressure.Concentration

namespace OAI

/-! Haar-direction comparison for the actual enriched Ising recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

private theorem vectorCascade_terminal_comparison {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    {F G : (Fin N → ℝ) → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFg : IsingPerceptron.HasLinearGrowth F) (hGg : IsingPerceptron.HasLinearGrowth G)
    {C : ℝ} (hFG : ∀ z, |F z - G z| ≤ C) (z : Fin N → ℝ) :
    |IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
        (fun _ p => p.1 + p.2) F z -
      IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
        (fun _ p => p.1 + p.2) G z| ≤ C := by
  induction n generalizing b v z with
  | zero => exact hFG z
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let F' := IsingPerceptron.cascadeRecursion n bs (fun i => vectorGaussianLaw N (vs i))
      (fun _ p => p.1 + p.2) F
    let G' := IsingPerceptron.cascadeRecursion n bs (fun i => vectorGaussianLaw N (vs i))
      (fun _ p => p.1 + p.2) G
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hmF : Measurable F' := IsingPerceptron.measurable_cascadeRecursion n bs
      (fun i => vectorGaussianLaw N (vs i)) (fun _ => measurable_fst.add measurable_snd) hF
    have hmG : Measurable G' := IsingPerceptron.measurable_cascadeRecursion n bs
      (fun i => vectorGaussianLaw N (vs i)) (fun _ => measurable_fst.add measurable_snd) hG
    have hgF : IsingPerceptron.HasLinearGrowth F' :=
      IsingPerceptron.cascadeRecursion_linearGrowth n bs (fun i => vectorGaussianLaw N (vs i))
        (fun i _ => vectorGaussianLaw_moments hN (vs i)) hF hFg hbs
    have hgG : IsingPerceptron.HasLinearGrowth G' :=
      IsingPerceptron.cascadeRecursion_linearGrowth n bs (fun i => vectorGaussianLaw N (vs i))
        (fun i _ => vectorGaussianLaw_moments hN (vs i)) hG hGg hbs
    have hiF : Integrable (fun g => Real.exp (b 0 * F' (z + g)))
        (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) :=
      IsingPerceptron.integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN (v 0))
        (hmF.comp (measurable_const.add measurable_id)) (hgF.add_left z) (b 0)
    have hiG : Integrable (fun g => Real.exp (b 0 * G' (z + g)))
        (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) :=
      IsingPerceptron.integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN (v 0))
        (hmG.comp (measurable_const.add measurable_id)) (hgG.add_left z) (b 0)
    exact IsingPerceptron.logMean_abs_sub_le _ (hb 0 (by omega)) hiF hiG
      (fun g => ih bs vs hbs (z + g))

theorem abs_rotatedCascadeValue_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (eig : Fin N → ℝ) (U V : SpecialOrthogonal N) (c z : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedCascadeValue n b v eig (specialRotation U) c z -
      rotatedCascadeValue n b v eig (specialRotation V) c z| ≤
      K * N * frobeniusDistance U V := by
  apply vectorCascade_terminal_comparison hN n b v (fun i hi => (hb.1 i hi).1)
    (measurable_rotatedFieldTerminal eig (specialRotation U) c)
    (measurable_rotatedFieldTerminal eig (specialRotation V) c)
    (rotatedFieldTerminal_linearGrowth eig (specialRotation U) c)
    (rotatedFieldTerminal_linearGrowth eig (specialRotation V) c)
  intro y
  apply abs_logPartition_sub_le
  intro σ
  simpa only [add_sub_add_right_eq_sub] using
    abs_rotatedEnergy_sub_rotation_le eig U V K hK heig σ

theorem abs_rotatedEnrichedPressure_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (root : ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (eig : Fin N → ℝ)
    (U V : SpecialOrthogonal N) (c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedEnrichedPressure n b v root eig (specialRotation U) c -
      rotatedEnrichedPressure n b v root eig (specialRotation V) c| ≤
      K * frobeniusDistance U V := by
  have hIU := integrable_rotatedCascadeValue hN n b v hb eig (specialRotation U) c root
  have hIV := integrable_rotatedCascadeValue hN n b v hb eig (specialRotation V) c root
  have hi := norm_integral_le_of_norm_le_const
    (μ := (vectorGaussianLaw N root : Measure (Fin N → ℝ)))
    (f := fun z => rotatedCascadeValue n b v eig (specialRotation U) c z -
      rotatedCascadeValue n b v eig (specialRotation V) c z)
    (C := K * N * frobeniusDistance U V) (ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using
        abs_rotatedCascadeValue_sub_rotation_le hN n b v hb eig U V c z K hK heig)
  have hI : |∫ z, (rotatedCascadeValue n b v eig (specialRotation U) c z -
      rotatedCascadeValue n b v eig (specialRotation V) c z)
      ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))| ≤ K * N * frobeniusDistance U V := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  unfold rotatedEnrichedPressure
  rw [← mul_sub, ← integral_sub hIU hIV, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    _ ≤ (N : ℝ)⁻¹ * (K * N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp

end InvariantIsing

end

end OAI
