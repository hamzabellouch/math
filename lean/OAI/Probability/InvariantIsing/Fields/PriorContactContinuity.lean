import OAI.Probability.InvariantIsing.Fields.PriorSiteModulus
import OAI.Probability.InvariantIsing.Fields.PriorTemperatureModulus
import OAI.Probability.InvariantIsing.Arrays.TensorContactRegion

namespace OAI

/-! Joint continuity of the constrained-prior contact pressure, including
zero covariance increments and both complete perturbation amplitudes. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology NNReal
namespace InvariantIsing

def priorContactPressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (p : TensorContactParameter N m n) : ℝ :=
  priorPerturbationPressureMean μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 -
    finiteFieldPath p.2.1 n/2

lemma priorContact_raw_modulus
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (p q : TensorContactParameter N m n)
    (hp : ∀ i, 0 ≤ p.2.1 i) (hq : ∀ i, 0 ≤ q.2.1 i) :
    |priorPerturbationPressureMean μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2-
      priorPerturbationPressureMean μ ν eig c I q.1 (finiteFieldPath q.2.1) q.2.2.1 q.2.2.2| ≤
    (K/2)*|p.1-q.1|+
      2*∑ i : Fin (n+1),
        |(NNReal.sqrt (varianceIncrement (finiteFieldPath p.2.1) i) : ℝ)-
          (NNReal.sqrt (varianceIncrement (finiteFieldPath q.2.1) i) : ℝ)| *
        ((NNReal.sqrt (varianceIncrement (finiteFieldPath p.2.1) i) : ℝ)+
          (NNReal.sqrt (varianceIncrement (finiteFieldPath q.2.1) i) : ℝ))+
      2*(N : ℝ)⁻¹*tensorAmplitudeModulus (tensorPerturbationAmplitude N p.2.2.1)
        (tensorPerturbationAmplitude N q.2.2.1)+perturbationScale N*∑ a, |p.2.2.2 a-q.2.2.2 a| := by
  let F := fun (t : ℝ) (a : Fin (n+1) → ℝ) (u : Fin N → ℝ) (v : Fin m → ℝ) =>
    priorPerturbationPressureMean μ ν eig c I t (finiteFieldPath a) u v
  have ht := priorPerturbationPressureMean_temperature_modulus hhaar hgauss hN μ hμ ν eig c I
    (finiteFieldPath p.2.1) (monotone_finiteFieldPath hp) (finiteFieldPath_nonneg hp 0)
    p.2.2.1 p.2.2.2 K hK p.1 q.1
  have ha := prior_site_pressure_modulus hhaar hgauss hN μ hμ ν
    (diagonalPerturbedEigenvalues eig I p.2.2.2 q.1) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    (fun i (j : Fin N) => varianceIncrement (monomialPath n (enumeratedTreeDegree m j)) i)
    (fun i => varianceIncrement (finiteFieldPath p.2.1) i)
    (fun i => varianceIncrement (finiteFieldPath q.2.1) i)
  change |F q.1 p.2.1 p.2.2.1 p.2.2.2-F q.1 q.2.1 p.2.2.1 p.2.2.2| ≤ _ at ha
  have hu := priorPerturbationPressureMean_modulus hhaar hgauss hN μ hμ ν eig c I q.1
    (finiteFieldPath q.2.1) (monotone_finiteFieldPath hq) (finiteFieldPath_nonneg hq 0)
    p.2.2.1 q.2.2.1 p.2.2.2 q.2.2.2
  have h1 := abs_sub_le (F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (F q.1 p.2.1 p.2.2.1 p.2.2.2) (F q.1 q.2.1 p.2.2.1 p.2.2.2)
  have h2 := abs_sub_le (F p.1 p.2.1 p.2.2.1 p.2.2.2)
    (F q.1 q.2.1 p.2.2.1 p.2.2.2) (F q.1 q.2.1 q.2.2.1 q.2.2.2)
  change |F p.1 p.2.1 p.2.2.1 p.2.2.2-F q.1 q.2.1 q.2.2.1 q.2.2.2| ≤ _
  linarith

lemma continuous_finiteFieldPath {n : ℕ} (i : ℕ) :
    Continuous (fun a : Fin (n+1) → ℝ => finiteFieldPath a i) := by
  unfold finiteFieldPath
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

lemma continuous_finiteFieldVariance {n : ℕ} (i : ℕ) :
    Continuous (fun a : Fin (n+1) → ℝ => varianceIncrement (finiteFieldPath a) i) := by
  cases i with
  | zero =>
    have h := continuous_finiteFieldPath (n := n) 0
    change Continuous (fun a : Fin (n+1) → ℝ => (finiteFieldPath a 0).toNNReal)
    fun_prop
  | succ i =>
    have h1 := continuous_finiteFieldPath (n := n) (i+1)
    have h2 := continuous_finiteFieldPath (n := n) i
    change Continuous (fun a : Fin (n+1) → ℝ =>
      (finiteFieldPath a (i+1)-finiteFieldPath a i).toNNReal)
    fun_prop

lemma continuousOn_priorContactPressure
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) {S : Set (TensorContactParameter N m n)}
    (hS : ∀ p ∈ S, ∀ i, 0 ≤ p.2.1 i) :
    ContinuousOn (priorContactPressure μ ν eig c I) S := by
  have hraw : ContinuousOn (fun p : TensorContactParameter N m n =>
      priorPerturbationPressureMean μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_iff_continuousAt.mpr
    intro q
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let D := fun p : S => (K/2)*|p.val.1-q.val.1|+
      2*∑ i : Fin (n+1),
        |(NNReal.sqrt (varianceIncrement (finiteFieldPath p.val.2.1) i) : ℝ)-
          (NNReal.sqrt (varianceIncrement (finiteFieldPath q.val.2.1) i) : ℝ)| *
        ((NNReal.sqrt (varianceIncrement (finiteFieldPath p.val.2.1) i) : ℝ)+
          (NNReal.sqrt (varianceIncrement (finiteFieldPath q.val.2.1) i) : ℝ))+
      2*(N : ℝ)⁻¹*tensorAmplitudeModulus (tensorPerturbationAmplitude N p.val.2.2.1)
        (tensorPerturbationAmplitude N q.val.2.2.1)+perturbationScale N*∑ a, |p.val.2.2.2 a-q.val.2.2.2 a|
    have hs (i : Fin (n+1)) : Continuous (fun p : S =>
        varianceIncrement (finiteFieldPath p.val.2.1) i) :=
      (continuous_finiteFieldVariance i).comp (by fun_prop)
    have hD : Continuous D := by
      unfold D tensorAmplitudeModulus tensorPerturbationAmplitude
      fun_prop
    have hz : D q=0 := by simp [D, tensorAmplitudeModulus]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun p => by
        simpa only [Real.norm_eq_abs, domRestrict_apply] using priorContact_raw_modulus
          hhaar hgauss hN μ hμ ν eig c I K hK p.val q.val (hS p.val p.property) (hS q.val q.property))
    simpa only [hz] using hD.tendsto q
  unfold priorContactPressure
  apply hraw.sub
  exact (((continuous_finiteFieldPath n).comp (by fun_prop)).div_const 2).continuousOn

end InvariantIsing

end

end OAI
