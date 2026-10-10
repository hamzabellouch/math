import OAI.Probability.InvariantIsing.Fields.SpinPriorContactMinimum
import OAI.Probability.InvariantIsing.Fields.SpinPriorGeometricLimit

namespace OAI

/-! Geometric GG limits at the same joint constrained-prior contact minima.
The perturbation parameters are not reselected after minimizing temperature
and field, so subsequent contact inequalities refer to this same sequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorContact_minimizers_have_GG_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (w : Fin (n+1) → ℝ) (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) b w S V (p k) ≤
        spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) b w S V q) :
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)),
      ∃ q : Fin (m+1) → Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ (φ k)) (π (φ k)) b
        (eig (φ k)) (c (φ k)) (I (φ k))
        (p (φ k)).2.2.1 (p (φ k)).2.2.2 (p (φ k)).1 (finiteFieldPath (p (φ k)).2.1))
        atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) := by
  have hbounds k := tensorContactRegion_bounds (hp k)
  have ht k : |(p k).1| ≤ 1 := by
    rw [abs_of_nonneg (hbounds k).1.1]
    exact (hbounds k).1.2
  have hh k : Monotone (finiteFieldPath (p k).2.1) := monotone_finiteFieldPath (hbounds k).2.1
  have h0 k : 0 ≤ finiteFieldPath (p k).2.1 0 := finiteFieldPath_nonneg (hbounds k).2.1 0
  have hcap k : finiteFieldPath (p k).2.1 n ≤ H := by
    rw [finiteFieldPath_last]
    exact (hbounds k).2.2.1
  exact spinPrior_minimizers_geometric_GG_limit hhaar hgauss N hN hNlim m n μ hμinv π b hb
    eig c K hK heig I (fun k => (p k).1) ht (fun k => finiteFieldPath (p k).2.1) hh h0 H hcap
    (fun k => (p k).2.2.1) (fun k => (hbounds k).2.2.2.1)
    (fun k => (p k).2.2.2) (fun k => (hbounds k).2.2.2.2)
    (fun k => spinPriorContact_minimum_perturbations (μ k) (π k) (eig k) (c k) (I k) b
      w S V H (p k) (hp k) (hmin k))

end InvariantIsing

end

end OAI
