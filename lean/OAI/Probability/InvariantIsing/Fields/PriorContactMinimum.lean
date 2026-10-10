import OAI.Probability.InvariantIsing.Fields.PriorContactContinuity

namespace OAI

/-! Joint contact minima for a fixed spin/leaf prior. The temperature scales
only the original interaction, and a joint minimum supplies the actual
perturbation minimum required by the constrained-prior GG construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def priorContactObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  -priorContactPressure μ ν eig c I p - (∑ i, w i*finiteFieldPath p.2.1 i)/2 +
    S+V p.1 + ∑ j : Fin N, perturbationWeight j*(p.2.2.1 j-3/2)^2 +
    ∑ a, (p.2.2.2 a-3/2)^2

lemma continuousOn_priorContactObjective (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) :
    ContinuousOn (priorContactObjective μ ν eig c I w S V) (tensorContactRegion N m n H) := by
  have hp := continuousOn_priorContactPressure hhaar hgauss hN μ hμ ν eig c I K hK
    (S := tensorContactRegion N m n H)
    (fun p hp => (tensorContactRegion_bounds hp).2.1)
  have hw : Continuous (fun p : TensorContactParameter N m n =>
      ∑ i, w i*finiteFieldPath p.2.1 i) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul ((continuous_finiteFieldPath i).comp (by fun_prop))
  unfold priorContactObjective
  exact (((hp.neg.sub (hw.div_const 2).continuousOn).add continuousOn_const).add
    (hV.comp continuous_fst).continuousOn |>.add (by fun_prop)).add (by fun_prop)

theorem priorContactObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) (hH : 0 ≤ H) :
    ∃ p ∈ tensorContactRegion N m n H,
      ∀ q ∈ tensorContactRegion N m n H,
        priorContactObjective μ ν eig c I w S V p ≤ priorContactObjective μ ν eig c I w S V q :=
  (isCompact_tensorContactRegion N m n H).exists_isMinOn
    (tensorContactRegion_nonempty N m n hH)
    (continuousOn_priorContactObjective hhaar hgauss hN μ hμ ν eig c I K hK w S V hV H)

lemma priorContactObjective_eq_perturbation {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) :
    priorContactObjective μ ν eig c I w S V p =
      priorPerturbationObjective μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 +
        finiteFieldPath p.2.1 n/2 - (∑ i, w i*finiteFieldPath p.2.1 i)/2+S+V p.1 := by
  unfold priorContactObjective priorContactPressure priorPerturbationObjective
  ring

theorem priorContact_minimum_perturbations {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : TensorContactParameter N m n) (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      priorContactObjective μ ν eig c I w S V p ≤ priorContactObjective μ ν eig c I w S V q) :
    ∀ u v, (∀ j, u j ∈ Icc (1 : ℝ) 2) → (∀ a, v a ∈ Icc (1 : ℝ) 2) →
      priorPerturbationObjective μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 ≤
        priorPerturbationObjective μ ν eig c I p.1 (finiteFieldPath p.2.1) u v := by
  intro u v hu hv
  let q : TensorContactParameter N m n := (p.1,p.2.1,u,v)
  obtain ⟨ht,ha,hcap,_,_⟩ := tensorContactRegion_bounds hp
  have hq : q ∈ tensorContactRegion N m n H := tensorContactRegion_mem ht ha hcap hu hv
  have h := hmin q hq
  rw [priorContactObjective_eq_perturbation μ ν eig c I w S V p,
    priorContactObjective_eq_perturbation μ ν eig c I w S V q] at h
  dsimp only [q] at h
  linarith

end InvariantIsing

end

end OAI
