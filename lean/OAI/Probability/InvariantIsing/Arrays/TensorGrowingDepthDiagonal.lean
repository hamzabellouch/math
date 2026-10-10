import OAI.Probability.InvariantIsing.Arrays.TensorLimitingDiagonal

namespace OAI

/-! Constant limiting diagonals for growing finite cascades, under the
explicit diagonal fluctuation rate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem tensor_growing_depth_minimizers_constantDiagonal
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ → ℕ) (_hN : ∀ k, 3 ≤ N k) (_hNlim : Tendsto N atTop atTop)
    (m : ℕ) (depth : ℕ → ℕ) (b : ℕ → ℕ → ℝ)
    (_hb : ∀ k, CascadeExponents (depth k) (b k))
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (_hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (_hK : 0 < K)
    (_heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (_hu : ∀ k j, u k j ∈ Set.Icc (1 : ℝ) 2)
    (v : ℕ → Fin m → ℝ) (_hv : ∀ k a, v k a ∈ Set.Icc (1 : ℝ) 2)
    (t : ℕ → ℝ) (_ht : ∀ k, |t k| ≤ 1)
    (h : ℕ → ℕ → ℝ) (_hh : ∀ k, Monotone (h k)) (_h0 : ∀ k, 0 ≤ h k 0)
    (H : ℝ) (_hH : ∀ k, h k (depth k) ≤ H)
    (_hmin : ∀ k u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) (depth k) (b k) (h k) (u k) (v k) ≤
        tensorPerturbationObjective (μ k) (eig k) (c k) (I k) (t k) (depth k) (b k) (h k) u' v')
    (_hrate : Tendsto (fun k => diagonalContactRate (N k)
      (4*(∫ T, (Real.log (rawTreeTotal (depth k) T).toReal)^2
        ∂(rawCascadeLaw (depth k) (b k) : Measure (RawTree (depth k))))+
        H+4+C*(K+4*m+8)^2)) atTop (𝓝 0))
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (_hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) (depth k) (b k) (h k))
      atTop (nhds Q))
    (q : Fin (m + 1) → ℝ)
    (_hc : Tendsto (fun k a => (tensorMinimumArrayDiagonal (N k) (depth k) (v k) a : ℝ)) atTop (nhds q)),
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i, i) a : ℝ) = q a := by
  obtain ⟨C, hC, hbound⟩ := tensorPerturbation_minimizers_diagonal_bound hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN hNlim m depth b hb μ hμ hμinv eig c K hK heig I u hu v hv t ht h hh h0 H hH hmin hrate Q hL q hc
  apply spectralArray_constant_diagonal_of_weak_limit _ Q hL _ q hc
  intro i a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [tensorMinimumArrayDiagonal, Fin.lastCases_last,
      tensorPerturbedArrayLaw, tensorNamespacedArrayLaw_treeDiagonal]
    exact tendsto_const_nhds
  · let L := fun k => 4 * (∫ T, (Real.log (rawTreeTotal (depth k) T).toReal) ^ 2
      ∂(rawCascadeLaw (depth k) (b k) : Measure (RawTree (depth k)))) + H + 4 + C * (K + 4 * m + 8) ^ 2
    have he : ∀ᶠ k in atTop, perturbationScale (N k) ≤ 1 / 32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k) ≤ 1 / 4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg (fun x => abs_nonneg _)) _
      hrate
    filter_upwards [he, hs] with k he hs
    have hd := hbound (N k) (hN k) (μ k) (hμinv k) m (eig k) (c k) K hK (heig k)
      (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k) (depth k) (b k) (hb k) (h k) (hh k) (h0 k) H (hH k)
      he hs (hmin k) i a
    simpa only [tensorPerturbedArrayLaw, tensorMinimumArrayDiagonal, Fin.lastCases_castSucc,
      Function.comp_def, L] using hd

end InvariantIsing

end

end OAI
