import OAI.Probability.InvariantIsing.Arrays.TensorContactMinimum
import OAI.Probability.InvariantIsing.Arrays.TensorLimitExistence

namespace OAI

/-! The GG subsequence is obtained from the same joint contact minima used
for the temperature and field inequalities. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_minimizers_have_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (w : Fin (n + 1) → ℝ) (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      tensorContactObjective (μ k) (eig k) (c k) (I k) b w S V (p k) ≤
        tensorContactObjective (μ k) (eig k) (c k) (I k) b w S V q) :
    ∃ Q : ProbabilityMeasure (SpectralArray (m + 1)),
      ∃ q : Fin (m + 1) → Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => tensorPerturbedArrayLaw (μ (φ k)) (eig (φ k)) (c (φ k)) (I (φ k))
        (p (φ k)).2.2.1 (p (φ k)).2.2.2 (p (φ k)).1 n b (finiteFieldPath (p (φ k)).2.1))
        atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) := by
  have hbounds k := tensorContactRegion_bounds (hp k)
  have ht k : |(p k).1| ≤ 1 := by
    rw [abs_of_nonneg (hbounds k).1.1]
    exact (hbounds k).1.2
  have hh k : Monotone (finiteFieldPath (p k).2.1) :=
    monotone_finiteFieldPath (hbounds k).2.1
  have h0 k : 0 ≤ finiteFieldPath (p k).2.1 0 :=
    finiteFieldPath_nonneg (hbounds k).2.1 0
  have hcap k : finiteFieldPath (p k).2.1 n ≤ H := by
    rw [finiteFieldPath_last]
    exact (hbounds k).2.2.1
  have hpert k := tensorContact_minimum_perturbations (μ k) (eig k) (c k) (I k) b hb
    w S V H (p k) (hp k) (hmin k)
  obtain ⟨Q, q, φ, hφ, hL, _, hgg, hd⟩ := tensorPerturbation_minimizers_have_GG_limit
    hhaar hgauss N hN hNlim m n b hb μ hμinv eig c K hK heig I
    (fun k => (p k).2.2.1) (fun k => (hbounds k).2.2.2.1)
    (fun k => (p k).2.2.2) (fun k => (hbounds k).2.2.2.2)
    (fun k => (p k).1) ht (fun k => finiteFieldPath (p k).2.1) hh h0 H hcap hpert
  exact ⟨Q, q, φ, hφ, hL, hgg, hd⟩

end InvariantIsing

end

end OAI
