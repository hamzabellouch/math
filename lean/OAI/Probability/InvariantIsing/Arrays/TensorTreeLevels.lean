import OAI.Probability.InvariantIsing.Arrays.TensorArrayGeometry
import OAI.Probability.InvariantIsing.Arrays.TensorLeafTail
import OAI.Probability.IsingPerceptron.OrderedQuantile

namespace OAI

/-! The tree coordinate of the actual tensor array remains on its finite
cascade levels after passage to a weak limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma spectralArrayLaw_treeLevels {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (i j : ℕ) :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    ((isClosed_treeLevels n).measurableSet.preimage (by fun_prop))]
  apply ae_of_all
  intro p
  simpa only [spectralReplicaArray, spectralJointEntry_tree] using
    treeOverlap_mem_levels n (p.2 i).2 (p.2 j).2

lemma tensorPerturbedArrayLaw_treeLevels {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (i j : ℕ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_treeLevels _ _ _ _ _ _ _ i j

lemma tensorPerturbedArrayLaw_limit_treeLevels (N : ℕ → ℕ) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q)) (i j : ℕ) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  exact ae_closed_of_weak_limit hL ((isClosed_treeLevels n).preimage (by fun_prop))
    (fun k => tensorPerturbedArrayLaw_treeLevels (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k) i j)


lemma tensorNamespacedArrayLaw_treeTail {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hb : CascadeExponents n b) (hh : Monotone h) (h0 : 0 ≤ h 0) (d : Fin n) :
    (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(tensorNamespacedArrayLaw μ eig c I degree amp n b r h : Measure (SpectralArray (m + 1)))) = 1 - b d := by
  have he := tensorNamespacedArrayLaw_test μ eig c I degree amp n b r h
    (fun x => treeTail n d (x (0,1) (Fin.last m) : ℝ))
    ((continuous_treeTail n d).comp (by fun_prop))
    (fun _ => tensorLeafPrefixTest (N := N) d) ![1,0]
    (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
    (by
      intro U σ
      simp only [spectralJointEntry_tree, tensorLeafPrefixTest,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact treeTail_overlap n d (σ 0).2 (σ 1).2)
  rw [he]
  exact tensorNamespacedReplicaAverage_leafPrefix hN μ eig c I degree amp n b r h hb hh h0 d

lemma tensorPerturbedArrayLaw_limit_treeTail (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) (h : ℕ → ℕ → ℝ)
    (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q)) (d : Fin n) :
    (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - b d := by
  have hi := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => treeTail n d (x (0,1) (Fin.last m) : ℝ),
        (continuous_treeTail n d).comp (by fun_prop)⟩)
  have he k := tensorNamespacedArrayLaw_treeTail (hN k) (μ k)
    (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude (N k) (u k))
    n b (fun j => enumeratedTreeDegree m j) (h k) hb (hh k) (h0 k) d
  have hconst : Tendsto (fun k => ∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k) :
        Measure (SpectralArray (m + 1)))) atTop (𝓝 (1 - b d)) := by
    simpa only [tensorPerturbedArrayLaw, he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 - b d) atTop (𝓝 (1 - b d)))
  exact tendsto_nhds_unique hi hconst

end InvariantIsing

end

end OAI
