import OAI.Probability.InvariantIsing.Fields.SpinPriorGeometricLimit
import OAI.Probability.InvariantIsing.Fields.SpinPriorLeafTail
import OAI.Probability.InvariantIsing.Arrays.TensorTreeLevels

namespace OAI

/-! Geometry and exact tree tails of the constrained cascade limit. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem spinPriorPerturbedArrayLaw_limit_geometry (N : ℕ → ℕ) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q)) :
    (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x) ∧
      ∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q := by
  constructor
  · exact spectralArray_limit_gram hL (fun k => spinPriorPerturbedArrayLaw_gram (n := n)
      (μ k) (π k) b (eig k) (c k) (I k) (u k) (v k) (t k) (h k))
  · intro e he
    exact spectralArray_limit_reindex hL e (fun k => spinPriorPerturbedArrayLaw_reindex (n := n)
      (μ k) (π k) b (eig k) (c k) (I k) (u k) (v k) (t k) (h k) e he)

lemma spinPriorPerturbedArrayLaw_treeLevels {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (i j : ℕ) :
    ∀ᵐ x ∂(spinPriorPerturbedArrayLaw (n := n) μ π b eig c I u v t h : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  unfold spinPriorPerturbedArrayLaw spinPriorArrayLaw
  exact spectralArrayLaw_treeLevels _ _ _ _ _ _ _ i j

lemma spinPriorPerturbedArrayLaw_limit_treeLevels (N : ℕ → ℕ) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q)) (i j : ℕ) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  exact ae_closed_of_weak_limit hL ((isClosed_treeLevels n).preimage (by fun_prop))
    (fun k => spinPriorPerturbedArrayLaw_treeLevels (μ k) (π k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k) i j)


lemma spinPriorArrayLaw_treeTail {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hb : CascadeExponents n b) (hh : Monotone h) (h0 : 0 ≤ h 0) (d : Fin n) :
    (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(spinPriorArrayLaw μ π eig c I degree amp n b r h : Measure (SpectralArray (m + 1)))) = 1 - b d := by
  have he := spinPriorArrayLaw_test μ π eig c I degree amp n b r h
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
  exact spinPriorReplicaAverage_leafPrefix hN μ π eig c I degree amp n b r h hb hh h0 d

lemma spinPriorPerturbedArrayLaw_limit_treeTail (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) (h : ℕ → ℕ → ℝ)
    (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q)) (d : Fin n) :
    (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - b d := by
  have hi := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => treeTail n d (x (0,1) (Fin.last m) : ℝ),
        (continuous_treeTail n d).comp (by fun_prop)⟩)
  have he k := spinPriorArrayLaw_treeTail (hN k) (μ k) (π k)
    (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude (N k) (u k))
    n b (fun j => enumeratedTreeDegree m j) (h k) hb (hh k) (h0 k) d
  have hconst : Tendsto (fun k => ∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) b (eig k) (c k) (I k) (u k) (v k) (t k) (h k) :
        Measure (SpectralArray (m + 1)))) atTop (𝓝 (1 - b d)) := by
    simpa only [spinPriorPerturbedArrayLaw, he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 - b d) atTop (𝓝 (1 - b d)))
  exact tendsto_nhds_unique hi hconst


end InvariantIsing

end

end OAI
