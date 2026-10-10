import OAI.Probability.InvariantIsing.Arrays.TensorAmplitudeComparison
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationObjective
import OAI.Probability.InvariantIsing.Arrays.FullPerturbationCost

namespace OAI

/-! Continuity and existence of genuine finite perturbation minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology NNReal ENNReal

namespace InvariantIsing

lemma tensorPathPressure_haar_mean (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m k : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (a : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) (h : ℕ → ℝ) :
    let v := tensorPathProfile I degree n r h
    let F := fun U : SpecialOrthogonal N =>
      tensorEnrichedPressure eig (specialRotation U) c I degree a n b (fun i => v (i + 1)) (v 0)
    Integrable F μ ∧
      (∫ p, tensorDisorderPressure eig c I degree a n p
        ∂μ.prod (tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0))) = ∫ U, F U ∂μ := by
  intro v F
  obtain ⟨C, hC, hv⟩ := tensorDisorderPressure_variance hhaar hgauss
  let K := 1 + ∑ i, |eig i|
  have hs : 0 ≤ ∑ i, |eig i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : 0 < K := by dsimp only [K]; linarith
  have heig : ∀ i, |eig i| ≤ K := fun i => by
    have hi := Finset.single_le_sum (f := fun i => |eig i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp only [K]
    linarith
  have hp := hv N hN μ inferInstance hμ m k eig c K hK heig I degree a n b hb
    (varianceIncrement h) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have hi := hp.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hm (U : SpecialOrthogonal N) : (∫ p, tensorDisorderPressure eig c I degree a n (U,p)
      ∂tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0)) = F U :=
    tensorDisorderPressure_conditional_mean hgauss (by omega) eig c U I degree a n b
      (fun i => v (i + 1)) hb (varianceIncrement h 0)
      (fun j => varianceIncrement (monomialPath n (r j)) 0)
  refine ⟨hi.integral_prod_left.congr (ae_of_all _ hm), ?_⟩
  calc
    _ = ∫ U, ∫ p, tensorDisorderPressure eig c I degree a n (U,p)
        ∂tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0) ∂μ := integral_prod _ hi
    _ = _ := integral_congr_ae (ae_of_all _ hm)

lemma rotatedEnergy_diagonal_difference_le {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v w : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    |rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ -
      rotatedEnergy (diagonalPerturbedEigenvalues eig I w t) U σ| ≤
      N * perturbationScale N * ∑ a, |v a - w a| := by
  have he : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [rotatedEnergy_diagonalPerturbation hN, rotatedEnergy_diagonalPerturbation hN,
    add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) * perturbationScale N by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (projectedOverlap_abs_le_one U (I a) σ σ)
    (abs_nonneg _)).trans_eq (mul_one _)

lemma tensorPerturbationPressureMean_modulus (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u u' : Fin N → ℝ) (v v' : Fin m → ℝ) :
    |tensorPerturbationPressureMean μ eig c I u v t n b h -
      tensorPerturbationPressureMean μ eig c I u' v' t n b h| ≤
      2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
        (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') +
        perturbationScale N * ∑ a, |v a - v' a| := by
  let d := fun j : Fin N => enumeratedSpectralDegree m j
  let r := fun j : Fin N => enumeratedTreeDegree m j
  let q := tensorPathProfile I d n r h
  let F := fun (u : Fin N → ℝ) (v : Fin m → ℝ) (U : SpecialOrthogonal N) =>
    tensorEnrichedPressure (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) c I d
      (tensorPerturbationAmplitude N u) n b (fun i => q (i + 1)) (q 0)
  have hrep (u : Fin N → ℝ) (v : Fin m → ℝ) : Integrable (F u v) μ ∧
      tensorPerturbationPressureMean μ eig c I u v t n b h = ∫ U, F u v U ∂μ :=
    tensorPathPressure_haar_mean hhaar hgauss hN μ hμ
      (diagonalPerturbedEigenvalues eig I v t) c I d (tensorPerturbationAmplitude N u) n r b hb h
  have hpoint (U : SpecialOrthogonal N) : |F u v U - F u' v' U| ≤
      2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
        (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') +
        perturbationScale N * ∑ a, |v a - v' a| := by
    have ha := tensorPathPressure_amplitude_comparison (by omega) (diagonalPerturbedEigenvalues eig I v t)
      c (specialRotation U) I d (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u')
      n r b hb h hh h0
    have hd := abs_tensorPathPressure_sub_base_le (by omega) (diagonalPerturbedEigenvalues eig I v t)
      (diagonalPerturbedEigenvalues eig I v' t) c (specialRotation U) I d
      (tensorPerturbationAmplitude N u') n r b hb h hh h0
      (N * perturbationScale N * ∑ a, |v a - v' a|)
      (rotatedEnergy_diagonal_difference_le (by omega) eig (specialRotation U) I v v' t)
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have he : (N : ℝ)⁻¹ * (N * perturbationScale N * ∑ a, |v a - v' a|) =
        perturbationScale N * ∑ a, |v a - v' a| := by field_simp
    rw [he] at hd
    exact (abs_sub_le _ _ _).trans (add_le_add ha hd)
  rw [(hrep u v).2, (hrep u' v').2, ← integral_sub (hrep u v).1 (hrep u' v').1,
    ← Real.norm_eq_abs]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hpoint U)

lemma continuous_tensorPerturbationPressureMean (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Continuous (fun p : (Fin N → ℝ) × (Fin m → ℝ) =>
      tensorPerturbationPressureMean μ eig c I p.1 p.2 t n b h) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let M := fun z : (Fin N → ℝ) × (Fin m → ℝ) =>
    2 * (N : ℝ)⁻¹ * tensorAmplitudeModulus
      (tensorPerturbationAmplitude N z.1) (tensorPerturbationAmplitude N p.1) +
      perturbationScale N * ∑ a, |z.2 a - p.2 a|
  have hc : Continuous M := by
    unfold M tensorAmplitudeModulus tensorPerturbationAmplitude
    fun_prop
  have hz : M p = 0 := by simp [M, tensorAmplitudeModulus]
  have ht : Tendsto M (𝓝 p) (𝓝 0) := by simpa only [hz] using hc.tendsto p
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, M] using tensorPerturbationPressureMean_modulus
      hhaar hgauss hN μ hμ eig c I t n b hb h hh h0 z.1 p.1 z.2 p.2) ht


lemma continuous_tensorPerturbationObjective (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Continuous (fun p : (Fin N → ℝ) × (Fin m → ℝ) =>
      tensorPerturbationObjective μ eig c I t n b h p.1 p.2) := by
  have hM := continuous_tensorPerturbationPressureMean hhaar hgauss hN μ hμ eig c I t n b hb h hh h0
  unfold tensorPerturbationObjective
  exact (hM.neg.add (by fun_prop)).add (by fun_prop)

private lemma finiteBox_minimum {N m : ℕ}
    (F : (Fin N → ℝ) × (Fin m → ℝ) → ℝ) (hF : Continuous F) :
    ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        F (u,v) ≤ F (u',v') := by
  let B := (Fin N → Set.Icc (1 : ℝ) 2) × (Fin m → Set.Icc (1 : ℝ) 2)
  let g : B → (Fin N → ℝ) × (Fin m → ℝ) := fun p => (fun j => p.1 j, fun a => p.2 a)
  have hg : Continuous g := by
    exact (continuous_pi fun j => continuous_subtype_val.comp
      ((continuous_apply j).comp continuous_fst)).prodMk
      (continuous_pi fun a => continuous_subtype_val.comp ((continuous_apply a).comp continuous_snd))
  let p₀ : B := (fun _ => ⟨1, by norm_num⟩, fun _ => ⟨1, by norm_num⟩)
  obtain ⟨p, _, hp⟩ := (isCompact_univ : IsCompact (Set.univ : Set B)).exists_isMinOn
    ⟨p₀, Set.mem_univ _⟩ (hF.comp hg).continuousOn
  refine ⟨fun j => p.1 j, fun a => p.2 a, fun j => (p.1 j).property,
    fun a => (p.2 a).property, ?_⟩
  intro u' v' hu' hv'
  exact hp (Set.mem_univ ((fun j => ⟨u' j, hu' j⟩, fun a => ⟨v' a, hv' a⟩) : B))

/-- The minimizers required by the GG/contact estimates exist for the actual
finite objective on the manuscript's compact perturbation box. -/
theorem tensorPerturbationObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective μ eig c I t n b h u v ≤
          tensorPerturbationObjective μ eig c I t n b h u' v' := by
  exact finiteBox_minimum
    (fun p => tensorPerturbationObjective μ eig c I t n b h p.1 p.2)
    (continuous_tensorPerturbationObjective hhaar hgauss hN μ hμ eig c I t n b hb h hh h0)

end InvariantIsing

end

end OAI
