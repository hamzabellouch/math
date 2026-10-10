import OAI.Probability.InvariantIsing.Fields.PriorTensorPressure
import OAI.Probability.InvariantIsing.Arrays.TensorObjectiveContinuity

namespace OAI

/-! Compact perturbation minima for a fixed constrained spin/leaf prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology NNReal
namespace InvariantIsing

def priorPerturbationPressureMean {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ p, priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) n
      (fun j => enumeratedTreeDegree m j) h i) p ∂μ.prod gaussianCoordinates

def priorPerturbationObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  -priorPerturbationPressureMean μ ν eig c I t h u v +
    ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2 + ∑ a, (v a-3/2)^2

lemma priorTensorLog_integrable (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m k n : ℕ} (hN : 3≤N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : Fin (n+1) → ℝ≥0) (monomial : Fin (n+1) → Fin k → ℝ≥0) :
    Integrable (priorTensorLog ν eig c I degree amplitude
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)))
      (μ.prod gaussianCoordinates) := by
  obtain ⟨C,hC,hv⟩ := priorTensorLog_variance hhaar hgauss
  have hs : 0≤∑ i, |eig i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : 0<1+∑ i, |eig i| := by linarith
  have he : ∀ i, |eig i|≤1+∑ i, |eig i| := fun i => by
    have hi := Finset.single_le_sum (f := fun j => |eig j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  exact (hv N hN μ inferInstance hμ m k n ν inferInstance eig c _ hK he I degree
    amplitude site monomial).1.integrable (by norm_num)

lemma priorPerturbationPressureMean_modulus (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3≤N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0)
    (u u' : Fin N → ℝ) (v v' : Fin m → ℝ) :
    |priorPerturbationPressureMean μ ν eig c I t h u v-
      priorPerturbationPressureMean μ ν eig c I t h u' v'| ≤
      2*(N : ℝ)⁻¹*tensorAmplitudeModulus
        (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') +
        perturbationScale N*∑ a, |v a-v' a| := by
  let d := fun j : Fin N => enumeratedSpectralDegree m j
  let r := fun j : Fin N => enumeratedTreeDegree m j
  let q := fun i : Fin (n+1) => tensorPathProfile I d n r h i
  let F := fun u v => priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) q
  have hi u v : Integrable (F u v) (μ.prod gaussianCoordinates) :=
    priorTensorLog_integrable hhaar hgauss hN μ hμ ν _ c I d _
      (fun i => varianceIncrement h i) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have hpoint U : |(∫ z, F u v (U,z) ∂gaussianCoordinates)-
      ∫ z, F u' v' (U,z) ∂gaussianCoordinates| ≤
      2*tensorAmplitudeModulus (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u')+
        N*perturbationScale N*∑ a, |v a-v' a| := by
    have ha := tensorPathLogMean_amplitude_comparison (specialRotation U) I d
      (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u') n r h hh h0 ν
      (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) x.1+
        fieldEnergy c x.1) (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) σ + fieldEnergy c σ))
    have hb := countable_cylinder_log_mean_base_compare ν
      (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) x.1+
        fieldEnergy c x.1)
      (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v' t) (specialRotation U) x.1+
        fieldEnergy c x.1)
      (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) σ + fieldEnergy c σ)) (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy (diagonalPerturbedEigenvalues eig I v' t) (specialRotation U) σ + fieldEnergy c σ))
      (tensorLeafCoefficients (specialRotation U) I d (tensorPerturbationAmplitude N u') n q)
      (tensorPathProfile_variance_cap (specialRotation U) I d (tensorPerturbationAmplitude N u')
        n r h hh h0)
      (fun x => by simpa only [add_sub_add_right_eq_sub] using
        rotatedEnergy_diagonal_difference_le (by omega) eig (specialRotation U) I v v' t x.1)
    exact (abs_sub_le _ _ _).trans (add_le_add ha hb)
  unfold priorPerturbationPressureMean
  change |(N : ℝ)⁻¹*(∫ p, F u v p ∂μ.prod gaussianCoordinates)-
    (N : ℝ)⁻¹*(∫ p, F u' v' p ∂μ.prod gaussianCoordinates)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)),
    integral_prod _ (hi u v), integral_prod _ (hi u' v'),
    ← integral_sub (hi u v).integral_prod_left (hi u' v').integral_prod_left]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => (∫ z, F u v (U,z) ∂gaussianCoordinates)-
      ∫ z, F u' v' (U,z) ∂gaussianCoordinates)
    (C := 2*tensorAmplitudeModulus (tensorPerturbationAmplitude N u) (tensorPerturbationAmplitude N u')+
      N*perturbationScale N*∑ a, |v a-v' a|)
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hpoint U)
  simp only [probReal_univ,mul_one,Real.norm_eq_abs] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (show 0≤(N : ℝ)⁻¹ by positivity)
  refine hb'.trans_eq ?_
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma continuous_priorPerturbationObjective (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3≤N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0) :
    Continuous (fun p : (Fin N → ℝ) × (Fin m → ℝ) =>
      priorPerturbationObjective μ ν eig c I t h p.1 p.2) := by
  have hM : Continuous (fun p : (Fin N → ℝ) × (Fin m → ℝ) =>
      priorPerturbationPressureMean μ ν eig c I t h p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let M := fun z : (Fin N → ℝ) × (Fin m → ℝ) =>
      2*(N : ℝ)⁻¹*tensorAmplitudeModulus (tensorPerturbationAmplitude N z.1)
        (tensorPerturbationAmplitude N p.1)+perturbationScale N*∑ a, |z.2 a-p.2 a|
    have hc : Continuous M := by
      unfold M tensorAmplitudeModulus tensorPerturbationAmplitude
      fun_prop
    have hz : M p=0 := by simp [M,tensorAmplitudeModulus]
    have ht : Filter.Tendsto M (𝓝 p) (𝓝 0) := by simpa only [hz] using hc.tendsto p
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,M] using priorPerturbationPressureMean_modulus
          hhaar hgauss hN μ hμ ν eig c I t h hh h0 z.1 p.1 z.2 p.2) ht
  unfold priorPerturbationObjective
  exact (hM.neg.add (by fun_prop)).add (by fun_prop)

private lemma priorFiniteBox_minimum {N m : ℕ}
    (F : (Fin N → ℝ) × (Fin m → ℝ) → ℝ) (hF : Continuous F) :
    ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j∈Icc (1 : ℝ) 2) ∧ (∀ a, v a∈Icc (1 : ℝ) 2) ∧
      ∀ u' v', (∀ j, u' j∈Icc (1 : ℝ) 2) → (∀ a, v' a∈Icc (1 : ℝ) 2) →
        F (u,v) ≤ F (u',v') := by
  let B := (Fin N → Icc (1 : ℝ) 2) × (Fin m → Icc (1 : ℝ) 2)
  let g : B → (Fin N → ℝ) × (Fin m → ℝ) := fun p => (fun j => p.1 j,fun a => p.2 a)
  have hg : Continuous g := by
    exact (continuous_pi fun j => continuous_subtype_val.comp
      ((continuous_apply j).comp continuous_fst)).prodMk
      (continuous_pi fun a => continuous_subtype_val.comp ((continuous_apply a).comp continuous_snd))
  let p₀ : B := (fun _ => ⟨1,by norm_num⟩,fun _ => ⟨1,by norm_num⟩)
  obtain ⟨p,_,hp⟩ := (isCompact_univ : IsCompact (univ : Set B)).exists_isMinOn
    ⟨p₀,mem_univ _⟩ (hF.comp hg).continuousOn
  exact ⟨fun j => p.1 j,fun a => p.2 a,fun j => (p.1 j).property,fun a => (p.2 a).property,
    fun u' v' hu' hv' => hp (mem_univ ((fun j => ⟨u' j,hu' j⟩,fun a => ⟨v' a,hv' a⟩) : B))⟩


theorem priorPerturbationObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3≤N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0) :
    ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j∈Icc (1 : ℝ) 2) ∧ (∀ a, v a∈Icc (1 : ℝ) 2) ∧
      ∀ u' v', (∀ j, u' j∈Icc (1 : ℝ) 2) → (∀ a, v' a∈Icc (1 : ℝ) 2) →
        priorPerturbationObjective μ ν eig c I t h u v ≤
          priorPerturbationObjective μ ν eig c I t h u' v' := by
  exact priorFiniteBox_minimum _
    (continuous_priorPerturbationObjective hhaar hgauss hN μ hμ ν eig c I t h hh h0)

end InvariantIsing

end

end OAI
