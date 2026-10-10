import OAI.Probability.InvariantIsing.Fields.PriorGGWardExistence
import OAI.Probability.InvariantIsing.Spectral.SpectralCanonicalIdentification
import OAI.Probability.InvariantIsing.Spectral.SpectralArrayEnergy
import OAI.Probability.InvariantIsing.Arrays.TensorSingleObservable

namespace OAI

/-! The original interaction energy in a constrained-prior GG limit is
identified by the actual rotation Ward equations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma priorNamespacedObservableAverage_eq_replica_one {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ) :
    priorNamespacedObservableAverage μ ν eig c I degree amp r h D =
      priorNamespacedReplicaAverage μ ν eig c I degree amp r h
        (fun U (σ : Fin 1 → Spin N × LabeledLeaf n) => D U (σ 0)) := by
  unfold priorNamespacedObservableAverage priorNamespacedReplicaAverage
  apply integral_congr_ae
  exact ae_of_all _ fun p => (referenceReplicaMean_zero_one
    (priorNamespacedReference ν eig c I degree amp (fun i => tensorPathProfile I degree n r h i) p)
    (D p.1)).symm

lemma priorNamespacedArrayLaw_interactionEnergy {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (modelEig energyEig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I=Finset.univ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → energyEig i=lam a)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    (∫ x, spectralArrayInteractionEnergy lam x
      ∂(priorNamespacedArrayLaw μ ν modelEig c I degree amp r h : Measure (SpectralArray (m+1)))) =
      priorNamespacedReplicaAverage μ ν modelEig c I degree amp r h
        (fun U (σ : Fin 1 → Spin N × LabeledLeaf n) =>
          (N : ℝ)⁻¹*rotatedEnergy energyEig (specialRotation U) (σ 0).1) := by
  apply priorNamespacedArrayLaw_test μ ν modelEig c I degree amp r h
    _ (continuous_spectralArrayInteractionEnergy lam) _ (fun i : Fin 1 => i.val) Fin.val_injective
  intro U σ
  simp only [spectralArrayInteractionEnergy, spectralJointEntry_spectral, Fin.val_zero]
  exact (normalized_rotatedEnergy_eq_blocks energyEig (specialRotation U) I hdis hcover lam hlam
    (σ 0).1).symm

theorem priorPerturbedArrayLaw_interactionEnergy_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i=lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))))
    (q : Fin (m+1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a)
    (ht₀ : 0 ≤ t₀) :
    ∃ hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x,
    ∃ hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0 ≤ (x (0,1) a : ℝ),
      Tendsto (fun k => priorNamespacedObservableAverage (μ k) (ν k)
        (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
        (fun j : Fin (N k) => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude (N k) (u k))
        (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k)
        (fun U x => (N k : ℝ)⁻¹*rotatedEnergy (eig k) (specialRotation U) x.1)) atTop
        (𝓝 (finiteInteractionEnergy ρ lam hρpos hρsum t₀ (spectralSpinQuantilePath Q hP hn))) := by
  have hG := spectralArray_limit_gram hL (fun k => priorPerturbedArrayLaw_gram
    (μ k) (ν k) (eig k) (c k) (I k) (u k) (v k) (t k) (h k))
  have hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q := by
    intro e he
    exact spectralArray_limit_reindex hL e (fun k => priorPerturbedArrayLaw_reindex
      (μ k) (ν k) (eig k) (c k) (I k) (u k) (v k) (t k) (h k) e he)
  have hP := spectralArray_limit_partition hL (fun k => priorPerturbedArrayLaw_partition
    (hN k) (μ k) (ν k) (eig k) (c k) (I k) (hdis k) (hcover k) (u k) (v k) (t k) (h k))
  have hn := spectralGG_coordinate_nonnegative hgg hG q hq hd
  obtain ⟨hoff,hdiag⟩ := priorPerturbedArrayLaw_ward_limits N hN hNlim m n μ hμinv ν
    eig c I hdis hcover lam hlam u hu v hv t ht h hh h0 Q hL ρ hρ
  have hid := spectralCanonical_identification hgg hG q hq hd hE hP hn
    ρ (fun a => t₀*lam a) hρpos hρsum hoff hdiag
  refine ⟨hP,hn,?_⟩
  have he k : (∫ x, spectralArrayInteractionEnergy lam x
      ∂(priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k) (u k) (v k) (t k) (h k) :
        Measure (SpectralArray (m+1)))) =
      priorNamespacedObservableAverage (μ k) (ν k)
        (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
        (fun j : Fin (N k) => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude (N k) (u k))
        (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k)
        (fun U x => (N k : ℝ)⁻¹*rotatedEnergy (eig k) (specialRotation U) x.1) := by
    rw [priorNamespacedObservableAverage_eq_replica_one]
    exact priorNamespacedArrayLaw_interactionEnergy (μ k) (ν k) _ (eig k) (c k) (I k)
      (hdis k) (hcover k) lam (hlam k) _ _ _ (h k)
  have hlim := spectralArrayInteractionEnergy_weak_limit hL lam
  simp_rw [he] at hlim
  rw [spectralArrayInteractionEnergy_eq_finiteEnergy Q q hd ρ lam hρpos hρsum ht₀
    (spectralSpinQuantilePath Q hP hn) hid.1] at hlim
  exact hlim

end InvariantIsing

end

end OAI
