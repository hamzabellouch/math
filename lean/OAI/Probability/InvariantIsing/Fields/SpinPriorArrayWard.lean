import OAI.Probability.InvariantIsing.Fields.SpinPriorPrincipalWard
import OAI.Probability.InvariantIsing.Fields.SpinPriorArrayLaw
import OAI.Probability.InvariantIsing.Arrays.TensorArrayWard

namespace OAI
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorArrayLaw_off_direct {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (b h : ℕ → ℝ) (treeDegree : Fin k → ℕ)
    (κ : Fin m → ℝ) (a b₀ : Fin m)
    (ha : ∀ i ∈ I a, eig i = κ a) (hb : ∀ i ∈ I b₀, eig i = κ b₀)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    (∫ x, spectralOffWardDirect (fun a => (I a).card / (N : ℝ)) κ a b₀ Φ x
      ∂(spinPriorArrayLaw μ π eig c I degree amp n b treeDegree h : Measure _)) =
    spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
      (fun U => tensorOffDirect eig (I a) (I b₀) (fun s : Spin N × LabeledLeaf n => s.1)
        (fun σ τ => Φ (spinPairOverlap σ τ)) U) := by
  apply spinPriorArrayLaw_test μ π eig c I degree amp n b treeDegree h _
    (continuous_spectralOffWardDirect _ _ _ _ Φ hΦ) _ Fin.val Fin.val_injective
  intro U σ
  rw [tensorOffDirect_eq_block eig (I a) (I b₀) (κ a) (κ b₀) ha hb]
  simp only [spectralOffWardDirect, spectralSpinArray_joint (specialRotation U) I hdis hcover,
    spectralJointEntry_spectral, tensorOffBlockDirect]
  rfl

lemma spinPriorArrayLaw_off_fresh {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (b h : ℕ → ℝ) (treeDegree : Fin k → ℕ)
    (κ : Fin m → ℝ) (a b₀ : Fin m)
    (ha : ∀ i ∈ I a, eig i = κ a) (hb : ∀ i ∈ I b₀, eig i = κ b₀)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    (∫ x, spectralOffWardFresh κ a b₀ Φ x
      ∂(spinPriorArrayLaw μ π eig c I degree amp n b treeDegree h : Measure _)) =
    spinPriorReplicaAverage μ π eig c I degree amp n b treeDegree h
      (fun U => tensorOffFresh eig (I a) (I b₀) (fun s : Spin N × LabeledLeaf n => s.1)
        (fun σ τ => Φ (spinPairOverlap σ τ)) U) := by
  apply spinPriorArrayLaw_test μ π eig c I degree amp n b treeDegree h _
    (continuous_spectralOffWardFresh _ _ _ Φ hΦ) _ Fin.val Fin.val_injective
  intro U σ
  rw [tensorOffFresh_eq_block eig (I a) (I b₀) (κ a) (κ b₀) ha hb]
  simp only [spectralOffWardFresh, spectralSpinArray_joint (specialRotation U) I hdis hcover,
    spectralJointEntry_spectral, tensorOffBlockFresh]
  rfl

 theorem spinPriorArrayLaw_off_ward_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (κ : Fin m → ℝ) (a b₀ : Fin m) (hJK : Disjoint (I a) (I b₀))
    (ha : ∀ i ∈ I a, eig i = κ a) (hb : ∀ i ∈ I b₀, eig i = κ b₀)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (B : ℝ) (hB : 0 ≤ B) (hΦB : ∀ r, |Φ r| ≤ B) :
    |spectralOffWardResidual
      (spinPriorArrayLaw μ π eig c I degree (tensorPerturbationAmplitude N u) n b treeDegree h)
      (fun a => (I a).card / (N : ℝ)) κ a b₀ Φ| ≤ 192 * B * D * perturbationScale N ^ 2 := by
  rw [spectralOffWardResidual_eq_direct_fresh _ _ _ _ _ Φ hΦ,
    spinPriorArrayLaw_off_direct μ π eig c I hdis hcover degree _ b h treeDegree κ a b₀ ha hb Φ hΦ,
    spinPriorArrayLaw_off_fresh μ π eig c I hdis hcover degree _ b h treeDegree κ a b₀ ha hb Φ hΦ]
  exact spinPrior_off_principal_bound hN μ π eig c I degree treeDegree u hu D hD hdegree
    b h hh h0 (I a) (I b₀) hJK (fun σ τ => Φ (spinPairOverlap σ τ)) B hB
    (fun σ τ => hΦB (spinPairOverlap σ τ))

end InvariantIsing

end

end OAI
