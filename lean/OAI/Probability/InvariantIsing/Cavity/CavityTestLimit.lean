import OAI.Probability.InvariantIsing.Cavity.CavityReplicaTest

namespace OAI

/-! Vanishing covariance and deterministic errors imply convergence of
bounded cavity replica tests, even when the configuration space varies
with the system size. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_secant_error_tendsto {f δ : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ s : ℝ, 0 < s → ∀ᶠ N in atTop, |f N| ≤ δ N / s + C * s) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let s := ε / (2 * (C + 1))
  have hs : 0 < s := div_pos hε (by positivity)
  have hCs : C * s < ε / 2 := by
    have he : (C + 1) * s = ε / 2 := by
      dsimp [s]
      field_simp
    nlinarith
  have hd := hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε * s / 2 by positivity))
  filter_upwards [hd, hbound s hs] with N hN hb
  have hd' : δ N / s < ε / 2 := by
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt hb (by linarith)

theorem cavity_twoReplica_test_tendsto {X : ℕ → Type*}
    [∀ N, MeasurableSpace (X N)] [∀ N, Countable (X N)]
    [∀ N, MeasurableSingletonClass (X N)]
    (ν : (N : ℕ) → Measure (X N)) [∀ N, IsProbabilityMeasure (ν N)]
    (H J : (N : ℕ) → X N → ℝ) (F : (N : ℕ) → (Fin 2 → X N) → ℝ)
    (C A : (N : ℕ) → X N → ℕ →₀ ℝ)
    (M₀ M₁ B₀ B₁ K E : ℕ → ℝ) {B : ℝ}
    (hH : ∀ N x, |H N x| ≤ M₀ N) (hJ : ∀ N x, |J N x| ≤ M₁ N)
    (hC : ∀ N x, (C N x).sum (fun _ z => z ^ 2) ≤ B₀ N)
    (hA : ∀ N x, (A N x).sum (fun _ z => z ^ 2) ≤ B₁ N)
    (hK : ∀ N, 0 ≤ K N)
    (hcov : ∀ N x y, |cylinderCross (A N x) (A N y) -
      cylinderCross (C N x) (C N y)| ≤ K N)
    (hbase : ∀ N x, |H N x - J N x| ≤ E N)
    (hB : 0 ≤ B) (hF : ∀ N σ, |F N σ| ≤ B)
    (hK0 : Tendsto K atTop (𝓝 0)) (hE0 : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun N =>
      (∫ g : ℕ → ℝ, referenceReplicaMean (ν N)
        (fun x => H N x + cylinderField (C N x) g) (F N) ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, referenceReplicaMean (ν N)
        (fun x => J N x + cylinderField (A N x) g) (F N) ∂gaussianCoordinates)
      atTop (𝓝 0) := by
  apply cavity_secant_error_tendsto (C := B ^ 2 / 2) (by positivity)
    (δ := fun N => 16 * K N + 4 * E N)
  · simpa only [mul_zero, add_zero] using (hK0.const_mul 16).add (hE0.const_mul 4)
  · intro s hs
    exact Eventually.of_forall (fun N => by
      simpa only [div_mul_eq_mul_div] using cavity_twoReplica_test_comparison (ν N)
        (H N) (J N) (F N) (hH N) (hJ N) (C N) (A N) (hC N) (hA N)
        (hK N) (hcov N) (hbase N) hB (hF N) hs)

end InvariantIsing

end

end OAI
