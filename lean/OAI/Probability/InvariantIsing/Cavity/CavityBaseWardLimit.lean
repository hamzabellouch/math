import OAI.Probability.InvariantIsing.Cavity.CavityBasePerturbedLaw
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbedWardLimit

namespace OAI

/-! Both Ward identities for the physical base array. The SO law is
derived from its actual Haar eigenbasis, and its Gaussian realization is
identified by the full array-law equality. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_rotation_ward_limits
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m depth : ℕ)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) (b : ℕ → ℝ)
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => cavityRotationArrayLaw (μ k)
      (labeledCascadeLaw depth b : Measure (LabeledTree depth))
      (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (I k) (cavityBaseAmplitude (u k)))
      atTop (𝓝 Q))
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
    (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ r, |Φ r| ≤ B) →
      spectralOffWardResidual Q ρ (fun a => t₀*lam a) a b₀ Φ = 0) ∧
    (∀ a b₀, spectralDiagonalWardResidual Q ρ (fun a => t₀*lam a) a b₀ = 0) := by
  have hEq k := cavity_base_perturbed_array_law (depth := depth)
    (hN k) (μ k) (eig k) (I k) (u k) (v k) (t k) b
  simp_rw [hEq] at hL
  exact tensorPerturbedArrayLaw_ward_limits N hN hNlim m depth
    (fun k => cavityOrientedBaseLaw (hN k) (μ k))
    (fun k => cavityOrientedBaseLaw_leftInvariant (hN k) (μ k))
    eig (fun _ _ => 0) I hdis hcover lam hlam u hu v hv t ht b
    (fun _ _ => 0) (fun _ => monotone_const) (fun _ => le_rfl) Q hL ρ hρ

end InvariantIsing

end

end OAI
