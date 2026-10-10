import OAI.Probability.InvariantIsing.Fields.PriorLimitingGG
import OAI.Probability.InvariantIsing.Fields.PriorArrayDiagonal
import OAI.Probability.InvariantIsing.Arrays.TensorLimitingDiagonal

namespace OAI

/-! Deterministic diagonals in constrained-prior weak limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem priorPerturbation_minimizers_constantDiagonal
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K) (heig : ∀ k i, |eig k i|≤K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j∈Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a∈Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k|≤1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (H : ℝ) (hH : ∀ k, h k n≤H)
    (hmin : ∀ k u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) (u k) (v k)≤
        priorPerturbationObjective (μ k) (ν k) (eig k) (c k) (I k) (t k) (h k) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q))
    (q : Fin (m+1) → ℝ)
    (hc : Tendsto (fun k a => (tensorMinimumArrayDiagonal (N k) n (v k) a : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a := by
  obtain ⟨C,hC,hbound⟩ := priorPerturbation_minimum_bounds hhaar hgauss
  apply spectralArray_constant_diagonal_of_weak_limit _ Q hL _ q hc
  intro i a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [tensorMinimumArrayDiagonal,Fin.lastCases_last,
      priorPerturbedArrayLaw,priorNamespacedArrayLaw_treeDiagonal]
    exact tendsto_const_nhds
  · let L := H+4+C*(K+4*m+8)^2
    have he : ∀ᶠ k in atTop, perturbationScale (N k)≤1/32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k)≤1/4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg (fun x => abs_nonneg _)) _
      ((diagonalContactRate_tendsto L).comp hNlim)
    filter_upwards [he,hs] with k he hs
    have hd := (hbound (N k) (hN k) (μ k) inferInstance (hμinv k) m n (ν k) inferInstance
      (eig k) (c k) K hK (heig k) (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k)
      (h k) (hh k) (h0 k) H (hH k) he hs (hmin k)).1 a
    have hd' := (priorSpectralDiagonal_clipping (μ k) (ν k)
      (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
      (fun j : Fin (N k) => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude (N k) (u k))
      (fun j : Fin (N k) => enumeratedTreeDegree m j) (h k) a
      (diagonalMinimumCenter (N k) (v k a))).trans hd
    simpa only [priorPerturbedArrayLaw,tensorMinimumArrayDiagonal,Fin.lastCases_castSucc,
      priorNamespacedArrayLaw_spectralDiagonal,L,Function.comp_def] using hd'

end InvariantIsing

end

end OAI
