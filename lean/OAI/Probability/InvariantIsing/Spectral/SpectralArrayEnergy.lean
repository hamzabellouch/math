import OAI.Probability.InvariantIsing.Arrays.TensorArrayLaw
import OAI.Probability.InvariantIsing.Spectral.SpectralPartition
import OAI.Probability.InvariantIsing.Spectral.SpectralTemperature

namespace OAI

/-! The interaction before temperature multiplication is an exact bounded
continuous spectral-array observable, so its Gibbs mean passes to weak limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma normalized_rotatedEnergy_eq_blocks {N m : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → eig i = lam a) (σ : Spin N) :
    (N : ℝ)⁻¹ * rotatedEnergy eig U σ =
      (1 / 2 : ℝ) * ∑ a, lam a * projectedOverlap U (I a) σ σ := by
  classical
  have hs : (∑ a, ∑ i ∈ I a, eig i * (U (spinVector σ) i) ^ 2) =
      ∑ i, eig i * (U (spinVector σ) i) ^ 2 := by
    rw [← Finset.sum_biUnion (show Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin m))) I by simpa using hdis), hcover]
  have he : (∑ i, eig i * (U (spinVector σ) i) ^ 2) =
      ∑ a, lam a * ∑ i ∈ I a, (U (spinVector σ) i) ^ 2 := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hlam a i hi])
  simp only [rotatedEnergy, he, projectedOverlap, ← pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring_nf

def spectralArrayInteractionEnergy {m : ℕ} (lam : Fin m → ℝ)
    (x : SpectralArray (m + 1)) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, lam a * (x (0,0) a.castSucc : ℝ)

lemma continuous_spectralArrayInteractionEnergy {m : ℕ} (lam : Fin m → ℝ) :
    Continuous (spectralArrayInteractionEnergy lam) := by
  unfold spectralArrayInteractionEnergy
  fun_prop

lemma tensorNamespacedArrayLaw_interactionEnergy {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (modelEig energyEig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → energyEig i = lam a)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    (∫ x, spectralArrayInteractionEnergy lam x
      ∂(tensorNamespacedArrayLaw μ modelEig c I degree amp n b treeDegree h :
        Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ modelEig c I degree amp n b treeDegree h
        (fun U (σ : Fin 1 → Spin N × LabeledLeaf n) =>
          (N : ℝ)⁻¹ * rotatedEnergy energyEig (specialRotation U) (σ 0).1) := by
  apply tensorNamespacedArrayLaw_test μ modelEig c I degree amp n b treeDegree h
    _ (continuous_spectralArrayInteractionEnergy lam) _
    (fun i : Fin 1 => i.val) Fin.val_injective
  intro U σ
  simp only [spectralArrayInteractionEnergy, spectralJointEntry_spectral, Fin.val_zero]
  exact (normalized_rotatedEnergy_eq_blocks energyEig (specialRotation U) I hdis hcover lam hlam (σ 0).1).symm

lemma spectralArrayInteractionEnergy_weak_limit {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    (lam : Fin m → ℝ) :
    Tendsto (fun k => ∫ x, spectralArrayInteractionEnergy lam x
      ∂(L k : Measure (SpectralArray (m + 1)))) atTop
      (𝓝 (∫ x, spectralArrayInteractionEnergy lam x ∂(Q : Measure (SpectralArray (m + 1))))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_spectralArrayInteractionEnergy lam⟩)

lemma spectralArrayInteractionEnergy_eq_finiteEnergy {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath)
    (hdiag : ∀ a, q a.castSucc = spectralGroupDiagonal ρ (fun a => t * lam a) hρ hρsum p a) :
    (∫ x, spectralArrayInteractionEnergy lam x ∂(Q : Measure (SpectralArray (m + 1)))) =
      finiteInteractionEnergy ρ lam hρ hρsum t p := by
  rw [finiteInteractionEnergy_eq_groupDiagonal ρ lam hρ hρsum ht p]
  calc
    _ = ∫ _x : SpectralArray (m + 1), (1 / 2 : ℝ) * ∑ a, lam a * q a.castSucc
        ∂(Q : Measure (SpectralArray (m + 1))) := by
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      simp only [spectralArrayInteractionEnergy, hx]
    _ = _ := by simp only [integral_const, probReal_univ, one_smul, hdiag]

end InvariantIsing

end

end OAI
