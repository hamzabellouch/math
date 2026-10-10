import OAI.Probability.InvariantIsing.Arrays.TensorLimitingGG
import OAI.Probability.InvariantIsing.Arrays.TensorMinimizerDiagonal
import OAI.Probability.InvariantIsing.Spectral.SpectralArrayDiagonalLimit

namespace OAI

/-! Actual diagonal-minimum fluctuations give constant limiting diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorMinimumArrayDiagonal {m : ℕ} (N n : ℕ) (v : Fin m → ℝ) :
    Fin (m + 1) → Set.Icc (0 : ℝ) 1 :=
  Fin.lastCases ⟨(n : ℝ) / (n + 1 : ℕ), finiteTreeDiagonal_mem n⟩
    (fun a => ⟨spectralDiagonalCenter (diagonalMinimumCenter N (v a)), spectralDiagonalCenter_mem _⟩)

theorem tensorPerturbation_minimizers_constantDiagonal
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop)
    (m n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0 < K)
    (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (hH : ∀ k, h k n ≤ H)
    (hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) (u k) (v k) ≤
        tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) n b (h k) u' v')
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k))
      atTop (nhds Q))
    (q : Fin (m + 1) → ℝ)
    (hc : Tendsto (fun k a => (tensorMinimumArrayDiagonal (N k) n (v k) a : ℝ)) atTop (nhds q)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i, i) a : ℝ) = q a := by
  obtain ⟨C, hC, hbound⟩ := tensorPerturbation_minimizers_diagonal_bound hhaar hgauss
  apply spectralArray_constant_diagonal_of_weak_limit _ Q hL _ q hc
  intro i a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [tensorMinimumArrayDiagonal, Fin.lastCases_last,
      tensorPerturbedArrayLaw, tensorNamespacedArrayLaw_treeDiagonal]
    exact tendsto_const_nhds
  · let L := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
      ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 4 * m + 8) ^ 2
    have he : ∀ᶠ k in atTop, perturbationScale (N k) ≤ 1 / 32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k) ≤ 1 / 4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg (fun x => abs_nonneg _)) _
      ((diagonalContactRate_tendsto L).comp hNlim)
    filter_upwards [he, hs] with k he hs
    have hd := hbound (N k) (hN k) (μ k) (hμinv k) m (eig k) (c k) K hK (heig k)
      (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k) n b hb (h k) (hh k) (h0 k) H (hH k)
      he hs (hmin k) i a
    simpa only [tensorPerturbedArrayLaw, tensorMinimumArrayDiagonal, Fin.lastCases_castSucc,
      Function.comp_def, L] using hd

end InvariantIsing

end

end OAI
