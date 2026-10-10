import OAI.Probability.InvariantIsing.Arrays.TensorArrayGeometry

namespace OAI

/-! Total spin overlap and self normalization for a genuine spectral partition. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma projectedOverlap_partition {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ τ) = projectedOverlap U Finset.univ σ τ := by
  classical
  unfold projectedOverlap
  rw [← Finset.mul_sum]
  congr 1
  have hs := Finset.sum_biUnion (f := fun i => U (spinVector σ) i * U (spinVector τ) i)
    (show Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) I by simpa using hdis)
  rw [hcover] at hs
  exact hs.symm

lemma projectedOverlap_partition_self {N m : ℕ} (hN : 0 < N) (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ σ) = 1 := by
  rw [projectedOverlap_partition U I hdis hcover, projectedOverlap_univ]
  simp only [← pow_two, spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')

def spectralSpinArray {m : ℕ} (x : SpectralArray (m + 1)) : RealArray :=
  fun i j => ∑ a : Fin m, (x (i,j) a.castSucc : ℝ)

lemma continuous_spectralSpinArray (m : ℕ) : Continuous (spectralSpinArray (m := m)) := by
  unfold spectralSpinArray
  fun_prop

def SpectralPartitionGeometry (m : ℕ) (x : SpectralArray (m + 1)) : Prop :=
  (∀ i j, |spectralSpinArray x i j| ≤ 1) ∧ ∀ i, spectralSpinArray x i i = 1

lemma isClosed_spectralPartitionGeometry (m : ℕ) :
    IsClosed {x : SpectralArray (m + 1) | SpectralPartitionGeometry m x} := by
  unfold SpectralPartitionGeometry
  apply IsClosed.inter
  · change IsClosed {x : SpectralArray (m + 1) | ∀ i j, |spectralSpinArray x i j| ≤ 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le
      (by unfold spectralSpinArray; fun_prop) continuous_const
  · change IsClosed {x : SpectralArray (m + 1) | ∀ i, spectralSpinArray x i i = 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by unfold spectralSpinArray; fun_prop) continuous_const

lemma spectralReplicaArray_partition {Ω : Type*} {N m : ℕ} (hN : 0 < N)
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) :
    SpectralPartitionGeometry m (spectralReplicaArray U I n p) := by
  have he (i j : ℕ) : spectralSpinArray (spectralReplicaArray U I n p) i j =
      projectedOverlap (specialRotation (U p.1)) Finset.univ (p.2 i).1 (p.2 j).1 := by
    simp only [spectralSpinArray, spectralReplicaArray, spectralJointEntry_spectral]
    exact projectedOverlap_partition _ I hdis hcover _ _
  constructor
  · intro i j
    rw [he]
    exact projectedOverlap_abs_le_one _ _ _ _
  · intro i
    simpa only [spectralSpinArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_partition_self hN (specialRotation (U p.1)) I hdis hcover (p.2 i).1

lemma spectralArrayLaw_partition {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ} (hN : 0 < N)
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))),
      SpectralPartitionGeometry m x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    SpectralPartitionGeometry m x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralPartitionGeometry m).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_partition hN U I hdis hcover n)

lemma spectralArray_limit_partition {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x :=
  ae_closed_of_weak_limit hL (isClosed_spectralPartitionGeometry m) hG


lemma tensorPerturbedArrayLaw_partition {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      SpectralPartitionGeometry m x := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_partition hN _ _ _ _ hdis hcover _ _ _

lemma spectralPartition_diagonal_sum {m : ℕ} {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) :
    (∑ a : Fin m, q a.castSucc) = 1 := by
  obtain ⟨x, hx, hdx⟩ := (hP.and hd).exists
  simpa only [spectralSpinArray, hdx] using hx.2 0

lemma spectralPartition_spin_unit {m : ℕ} {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), spectralSpinArray x 0 1 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [hP, hn] with x hx hnx
  exact ⟨Finset.sum_nonneg (fun a _ => hnx a.castSucc), (le_abs_self _).trans (hx.1 0 1)⟩

def spectralSpinWeight (m : ℕ) : Fin (m + 1) → ℝ := Fin.lastCases 0 (fun _ => 1)

lemma spectralSpinWeight_nonneg (m : ℕ) (a : Fin (m + 1)) : 0 ≤ spectralSpinWeight m a := by
  refine Fin.lastCases ?_ (fun _ => ?_) a <;> simp [spectralSpinWeight]

lemma spectralLinearArray_spinWeight {m : ℕ} (x : SpectralArray (m + 1)) :
    spectralLinearArray (spectralSpinWeight m) x = spectralSpinArray x := by
  funext i j
  simp only [spectralLinearArray, spectralLinearEntry, Fin.sum_univ_castSucc,
    spectralSpinWeight, Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, zero_mul, add_zero,
    spectralSpinArray]

lemma spectralLinearArray_single {m : ℕ} (a : Fin m) (x : SpectralArray m) :
    spectralLinearArray (Pi.single a 1) x = spectralCoordinateArray a x := by
  classical
  funext i j
  simp [spectralLinearArray, spectralLinearEntry, spectralCoordinateArray, Pi.single_apply]

end InvariantIsing

end

end OAI
