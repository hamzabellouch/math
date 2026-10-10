import OAI.Probability.InvariantIsing.Arrays.TensorGrowingWard
import OAI.Probability.InvariantIsing.Arrays.TensorGrowingDiagonalWard
import OAI.Probability.InvariantIsing.Spectral.SpectralPerturbedBlocks

namespace OAI

/-! Both Ward equations for the growing-depth enriched model, with its
actual diagonal perturbation and complete monomial enumeration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorGrowingPerturbedArrayLaw_ward_limits
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m : ℕ) (depth : ℕ → ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (depth k) (b k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
    (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ r, |Φ r| ≤ B) →
      spectralOffWardResidual Q ρ (fun a => t₀ * lam a) a b₀ Φ = 0) ∧
    (∀ a b₀, spectralDiagonalWardResidual Q ρ (fun a => t₀ * lam a) a b₀ = 0) := by
  let E := fun k => diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)
  let κ := fun k a => t k * lam a + 2 * perturbationScale (N k) * v k a
  have hκ : ∀ k a i, i ∈ I k a → E k i = κ k a := fun k =>
    diagonalPerturbedEigenvalues_block (eig k) (I k) (hdis k) (v k) (t k) lam (hlam k)
  have hκlim : Tendsto κ atTop (𝓝 (fun a => t₀ * lam a)) :=
    perturbedBlockEigenvalues_tendsto N hNlim v hv t ht lam
  have hdegree (k : ℕ) (r : Fin (N k)) :
      (∑ a, (enumeratedSpectralDegree m r a : ℝ)) ≤ 1 * ((r : ℝ) + 1) := by
    simpa only [one_mul] using enumeratedSpectralDegree_real_sum_le m r
  refine ⟨?_, ?_⟩
  · intro a b₀ Φ hΦ B hB hΦB
    exact tensorGrowingArrayLaw_off_ward_limit N hN hNlim m depth μ hμinv E c I hdis hcover
      (fun k r => enumeratedSpectralDegree m r) (fun k r => enumeratedTreeDegree m r)
      u hu 1 zero_le_one hdegree b h hh h0 κ hκ Q hL ρ (fun a => t₀ * lam a)
      hρ hκlim a b₀ Φ hΦ B hB hΦB
  · intro a b₀
    by_cases hab : a = b₀
    · subst b₀
      simp [spectralDiagonalWardResidual]
    exact tensorGrowingArrayLaw_diagonalWard_limit N hN hNlim m depth μ hμinv E c I
      (fun k r => enumeratedSpectralDegree m r) (fun k r => enumeratedTreeDegree m r)
      u hu 1 zero_le_one hdegree b h hh h0 κ ρ (fun a => t₀ * lam a) hρ hκlim a b₀
      (fun k => hdis k (Set.mem_univ a) (Set.mem_univ b₀) hab)
      (fun k => hκ k a) (fun k => hκ k b₀) Q hL

end InvariantIsing

end

end OAI
