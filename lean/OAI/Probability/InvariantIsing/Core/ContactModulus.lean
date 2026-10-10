import OAI.Probability.InvariantIsing.Fields.PriorContactContinuity

namespace OAI

/-! A prior-independent joint modulus for centered contact pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal
namespace InvariantIsing

def contactModulus {N m n : ℕ} (K : ℝ) (p q : TensorContactParameter N m n) : ℝ :=
  (K/2)*|p.1-q.1|+
    2*∑ i : Fin (n+1),
      |(NNReal.sqrt (varianceIncrement (finiteFieldPath p.2.1) i) : ℝ)-
        (NNReal.sqrt (varianceIncrement (finiteFieldPath q.2.1) i) : ℝ)| *
      ((NNReal.sqrt (varianceIncrement (finiteFieldPath p.2.1) i) : ℝ)+
        (NNReal.sqrt (varianceIncrement (finiteFieldPath q.2.1) i) : ℝ))+
    2*(N : ℝ)⁻¹*tensorAmplitudeModulus (tensorPerturbationAmplitude N p.2.2.1)
      (tensorPerturbationAmplitude N q.2.2.1)+perturbationScale N*∑ a, |p.2.2.2 a-q.2.2.2 a|+
    |finiteFieldPath p.2.1 n-finiteFieldPath q.2.1 n|/2

lemma contactModulus_self {N m n : ℕ} (K : ℝ) (p : TensorContactParameter N m n) :
    contactModulus K p p=0 := by
  simp [contactModulus,tensorAmplitudeModulus]

lemma continuous_contactModulus {N m n : ℕ} (K : ℝ) (q : TensorContactParameter N m n) :
    Continuous (fun p : TensorContactParameter N m n => contactModulus K p q) := by
  have hs (i : Fin (n+1)) : Continuous (fun p : TensorContactParameter N m n =>
      varianceIncrement (finiteFieldPath p.2.1) i) :=
    (continuous_finiteFieldVariance i).comp (by fun_prop)
  have hf : Continuous (fun p : TensorContactParameter N m n => finiteFieldPath p.2.1 n) :=
    (continuous_finiteFieldPath n).comp (by fun_prop)
  unfold contactModulus tensorAmplitudeModulus tensorPerturbationAmplitude
  fun_prop

lemma priorContactPressure_modulus
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (p q : TensorContactParameter N m n)
    (hp : ∀ i, 0 ≤ p.2.1 i) (hq : ∀ i, 0 ≤ q.2.1 i) :
    |priorContactPressure μ ν eig c I p-priorContactPressure μ ν eig c I q| ≤ contactModulus K p q := by
  have hraw := priorContact_raw_modulus hhaar hgauss hN μ hμ ν eig c I K hK p q hp hq
  let A := priorPerturbationPressureMean μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2
  let B := priorPerturbationPressureMean μ ν eig c I q.1 (finiteFieldPath q.2.1) q.2.2.1 q.2.2.2
  have he : (A-finiteFieldPath p.2.1 n/2)-(B-finiteFieldPath q.2.1 n/2) =
      (A-B)-(finiteFieldPath p.2.1 n-finiteFieldPath q.2.1 n)/2 := by ring
  change |(A-finiteFieldPath p.2.1 n/2)-(B-finiteFieldPath q.2.1 n/2)| ≤ _
  rw [he]
  have ht := abs_sub (A-B) ((finiteFieldPath p.2.1 n-finiteFieldPath q.2.1 n)/2)
  rw [abs_div,abs_of_pos (show 0 < (2 : ℝ) by norm_num)] at ht
  exact ht.trans (add_le_add hraw le_rfl)

end InvariantIsing

end

end OAI
