import OAI.Probability.InvariantIsing.Fields.PriorContactMinimum
import OAI.Probability.InvariantIsing.Fields.PriorFixedGeometricLimit

namespace OAI

/-! Geometric GG limits at the same joint constrained-prior contact minima.
The perturbation parameters are not reselected after minimizing temperature
and field, so subsequent contact inequalities refer to this same sequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem priorContact_minimizers_have_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (w : Fin (n+1) → ℝ) (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      priorContactObjective (μ k) (ν k) (eig k) (c k) (I k) w S V (p k) ≤
        priorContactObjective (μ k) (ν k) (eig k) (c k) (I k) w S V q) :
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => priorPerturbedArrayLaw (μ (φ k)) (ν (φ k))
        (eig (φ k)) (c (φ k)) (I (φ k))
        (p (φ k)).2.2.1 (p (φ k)).2.2.2 (p (φ k)).1 (finiteFieldPath (p (φ k)).2.1))
        atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) := by
  have hb k := tensorContactRegion_bounds (hp k)
  have ht k : |(p k).1| ≤ 1 := by
    rw [abs_of_nonneg (hb k).1.1]
    exact (hb k).1.2
  have hh k : Monotone (finiteFieldPath (p k).2.1) := monotone_finiteFieldPath (hb k).2.1
  have h0 k : 0 ≤ finiteFieldPath (p k).2.1 0 := finiteFieldPath_nonneg (hb k).2.1 0
  have hcap k : finiteFieldPath (p k).2.1 n ≤ H := by
    rw [finiteFieldPath_last]
    exact (hb k).2.2.1
  exact prior_minimizers_geometric_GG_limit hhaar hgauss N hN hNlim m n μ hμinv ν
    eig c K hK heig I (fun k => (p k).1) ht (fun k => finiteFieldPath (p k).2.1) hh h0 H hcap
    (fun k => (p k).2.2.1) (fun k => (hb k).2.2.2.1)
    (fun k => (p k).2.2.2) (fun k => (hb k).2.2.2.2)
    (fun k => priorContact_minimum_perturbations (μ k) (ν k) (eig k) (c k) (I k)
      w S V H (p k) (hp k) (hmin k))

end InvariantIsing

end

end OAI
