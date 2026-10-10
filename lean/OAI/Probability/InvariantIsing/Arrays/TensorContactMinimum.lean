import OAI.Probability.InvariantIsing.Arrays.TensorContactContinuity

namespace OAI

/-! Actual finite joint contact minima. Restricting a joint minimum to the
two perturbation boxes gives exactly the minima used in the GG limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def tensorContactObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  -tensorContactPressure μ eig c I b p - (∑ i, w i * finiteFieldPath p.2.1 i) / 2 +
    S + V p.1 + ∑ j : Fin N, perturbationWeight j * (p.2.2.1 j - 3 / 2) ^ 2 +
    ∑ a, (p.2.2.2 a - 3 / 2) ^ 2

lemma continuousOn_tensorContactObjective (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) :
    ContinuousOn (tensorContactObjective μ eig c I b w S V) (tensorContactRegion N m n H) := by
  have hp := continuousOn_tensorContactPressure hhaar hgauss hN μ hμ eig c I b hb K hK
    (s := tensorContactRegion N m n H)
    (fun p hp => (tensorContactRegion_bounds hp).2.1)
  have hw : Continuous (fun p : TensorContactParameter N m n =>
      ∑ i, w i * finiteFieldPath p.2.1 i) := by
    unfold finiteFieldPath
    apply continuous_finsetSum
    intro i _
    apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    split_ifs <;> fun_prop
  unfold tensorContactObjective
  exact (((hp.neg.sub (hw.div_const 2).continuousOn).add continuousOn_const).add
    (hV.comp continuous_fst).continuousOn |>.add (by fun_prop)).add (by fun_prop)

theorem tensorContactObjective_exists_minimum (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (hV : Continuous V) (H : ℝ) (hH : 0 ≤ H) :
    ∃ p ∈ tensorContactRegion N m n H,
      ∀ q ∈ tensorContactRegion N m n H,
        tensorContactObjective μ eig c I b w S V p ≤ tensorContactObjective μ eig c I b w S V q :=
  (isCompact_tensorContactRegion N m n H).exists_isMinOn
    (tensorContactRegion_nonempty N m n hH)
    (continuousOn_tensorContactObjective hhaar hgauss hN μ hμ eig c I b hb K hK w S V hV H)

lemma tensorContactObjective_eq_perturbation {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (w : Fin (n + 1) → ℝ) (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) :
    tensorContactObjective μ eig c I b w S V p =
      tensorPerturbationObjective μ eig c I p.1 n b (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 +
        finiteFieldPath p.2.1 n / 2 - (∑ i, w i * finiteFieldPath p.2.1 i) / 2 + S + V p.1 := by
  unfold tensorContactObjective tensorContactPressure
  rw [tensorNamespacedMeanPressure_eq_perturbation μ eig c I p.2.2.1 p.2.2.2 p.1
    n b (finiteFieldPath p.2.1) hb]
  unfold tensorPerturbationObjective
  ring

theorem tensorContact_minimum_perturbations {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (w : Fin (n + 1) → ℝ) (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : TensorContactParameter N m n) (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      tensorContactObjective μ eig c I b w S V p ≤ tensorContactObjective μ eig c I b w S V q) :
    ∀ u v, (∀ j, u j ∈ Icc (1 : ℝ) 2) → (∀ a, v a ∈ Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I p.1 n b (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 ≤
        tensorPerturbationObjective μ eig c I p.1 n b (finiteFieldPath p.2.1) u v := by
  intro u v hu hv
  let q : TensorContactParameter N m n := (p.1, p.2.1, u, v)
  obtain ⟨ht, ha, hcap, _, _⟩ := tensorContactRegion_bounds hp
  have hq : q ∈ tensorContactRegion N m n H := tensorContactRegion_mem ht ha hcap hu hv
  have h := hmin q hq
  rw [tensorContactObjective_eq_perturbation μ eig c I b hb w S V p,
    tensorContactObjective_eq_perturbation μ eig c I b hb w S V q] at h
  dsimp only [q] at h
  linarith

end InvariantIsing

end

end OAI
