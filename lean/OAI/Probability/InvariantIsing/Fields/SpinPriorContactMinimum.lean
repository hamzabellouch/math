import OAI.Probability.InvariantIsing.Fields.SpinPriorContact

namespace OAI

/-! Joint contact minima for the actual cascade-enriched spin prior.
The pressure averages the logarithm over the quenched cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def spinPriorPerturbationPressureMean {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (t : ℝ) (h : ℕ → ℝ) (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  spinPriorMeanPressure (n := n) μ π (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    b (fun j : Fin N => enumeratedTreeDegree m j) h+h n/2

def spinPriorPerturbationObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (t : ℝ) (h : ℕ → ℝ) (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  -spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h u v+
    ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2+∑ a, (v a-3/2)^2

def spinPriorContactObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  -spinPriorContactPressure μ π eig c I b p - (∑ i, w i*finiteFieldPath p.2.1 i)/2 +
    S+V p.1 + ∑ j : Fin N, perturbationWeight j*(p.2.2.1 j-3/2)^2 +
    ∑ a, (p.2.2.2 a-3/2)^2

lemma continuousOn_spinPriorContactObjective (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) :
    ContinuousOn (spinPriorContactObjective μ π eig c I b w S V) (tensorContactRegion N m n H) := by
  have hp := continuousOn_spinPriorContactPressure hhaar hgauss hN μ hμ π eig c I b K hK
    (S := tensorContactRegion N m n H)
    (fun p hp => (tensorContactRegion_bounds hp).2.1)
  have hw : Continuous (fun p : TensorContactParameter N m n =>
      ∑ i, w i*finiteFieldPath p.2.1 i) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul ((continuous_finiteFieldPath i).comp (by fun_prop))
  unfold spinPriorContactObjective
  exact (((hp.neg.sub (hw.div_const 2).continuousOn).add continuousOn_const).add
    (hV.comp continuous_fst).continuousOn |>.add (by fun_prop)).add (by fun_prop)

theorem spinPriorContactObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) (hH : 0 ≤ H) :
    ∃ p ∈ tensorContactRegion N m n H,
      ∀ q ∈ tensorContactRegion N m n H,
        spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q :=
  (isCompact_tensorContactRegion N m n H).exists_isMinOn
    (tensorContactRegion_nonempty N m n hH)
    (continuousOn_spinPriorContactObjective hhaar hgauss hN μ hμ π eig c I b K hK w S V hV H)

lemma spinPriorContactObjective_eq_perturbation {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) :
    spinPriorContactObjective μ π eig c I b w S V p =
      spinPriorPerturbationObjective (n := n) μ π eig c I b p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 +
        finiteFieldPath p.2.1 n/2 - (∑ i, w i*finiteFieldPath p.2.1 i)/2+S+V p.1 := by
  unfold spinPriorContactObjective spinPriorContactPressure spinPriorPerturbationObjective spinPriorPerturbationPressureMean
  ring

theorem spinPriorContact_minimum_perturbations {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : TensorContactParameter N m n) (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q) :
    ∀ u v, (∀ j, u j ∈ Icc (1 : ℝ) 2) → (∀ a, v a ∈ Icc (1 : ℝ) 2) →
      spinPriorPerturbationObjective (n := n) μ π eig c I b p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 ≤
        spinPriorPerturbationObjective (n := n) μ π eig c I b p.1 (finiteFieldPath p.2.1) u v := by
  intro u v hu hv
  let q : TensorContactParameter N m n := (p.1,p.2.1,u,v)
  obtain ⟨ht,ha,hcap,_,_⟩ := tensorContactRegion_bounds hp
  have hq : q ∈ tensorContactRegion N m n H := tensorContactRegion_mem ht ha hcap hu hv
  have h := hmin q hq
  rw [spinPriorContactObjective_eq_perturbation μ π eig c I b w S V p,
    spinPriorContactObjective_eq_perturbation μ π eig c I b w S V q] at h
  dsimp only [q] at h
  linarith

end InvariantIsing

end

end OAI
