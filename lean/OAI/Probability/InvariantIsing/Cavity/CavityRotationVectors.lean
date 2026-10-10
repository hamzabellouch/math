import OAI.Probability.InvariantIsing.Cavity.CavityRotationArray

namespace OAI

/-! Measurable physical group vectors and their covariance in the actual
base Gibbs disorder space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRotationVectors {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (a : Fin m) (x : Spin N × LabeledLeaf depth) : Fin (k a) → ℝ :=
  cavityGroupSpinCoordinates k e p.1.1 a x.1

lemma measurable_cavityRotationVectors {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p a => cavityRotationVectors k e p a x) := by
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro j
  exact (measurable_cavityRotation_eval (spinVector x.1) (e ⟨a,j⟩)).comp measurable_fst.fst

lemma cavityRotationVectors_gram_bound {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth)))
    {c : ℝ} (hc : 0 < c) (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i)) a i j| ≤ 1/c :=
  cavityGroupSpinCoordinates_gram_bound hN k e p.1.1.1
    (fun i => (p.2 i).1) hc hk

lemma cavityRotationVectors_covariance {N m depth r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (ℕ → Spin N × LabeledLeaf depth))) (q : ℕ) :
    cavityGroupReplicaCovariance q (cavityGroupReplicaGram
      (fun a (i : Fin r) => cavityRotationVectors k e p.1 a (p.2 i))) =
    cavitySpectralBlockCovariance q (fun a => (k a : ℝ)/N)
      (spectralBlockView (m+1) r (cavitySampledEntryArray
        (cavityRotationEntry (cavitySpectralGroup (fun i => (e.symm i).1))) p)) :=
  cavityGroupSpinCoordinates_covariance hN k e p.1.1.1 (fun i => p.2 i) q

end InvariantIsing

end

end OAI
