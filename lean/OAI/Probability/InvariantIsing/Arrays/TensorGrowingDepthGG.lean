import OAI.Probability.InvariantIsing.Arrays.TensorLimitingGG

namespace OAI

/-! Full vector GG for growing finite cascades. The only additional
condition is the explicit vanishing finite-model rate, attainable by
choosing the system sizes along a sufficiently fast subsequence. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem tensor_growing_depth_minimizers_spectralGG
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
    (_hrate : ∀ j B, Tendsto (fun k => tensorContactGGRate (N k) j m
      (4*(∫ T, (Real.log (rawTreeTotal (depth k) T).toReal)^2
        ∂(rawCascadeLaw (depth k) (b k) : Measure (RawTree (depth k))))+
        H+4+C*(K+4*m+8)^2) B) atTop (𝓝 0))
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (_hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) (depth k) (b k) (h k))
      atTop (nhds Q)),
    HasEntryGhirlandaGuerra (fun x i j => x (i, j)) (Q : Measure (SpectralArray (m + 1))) := by
  obtain ⟨C, hC, hbound⟩ := tensorPerturbation_minimizers_arrayResidual_bound hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN hNlim m depth b hb μ hμ hμinv eig c K hK heig I u hu v hv t ht h hh h0 H hH hmin hrate Q hL
  apply spectralGG_of_weak_nonconstant_monomial_residuals hL
  intro z hz i D hD d hd
  cases z with
  | zero => omega
  | succ q =>
    obtain ⟨j, hj⟩ := enumeratedJointMonomial_surjective m d hd
    let BD := BoundedContinuousFunction.mkOfCompact ⟨D, hD⟩
    have hDb : ∀ x, |D x| ≤ ‖BD‖ := fun x => by
      simpa only [BD, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
        Real.norm_eq_abs] using BD.norm_coe_le_norm x
    let L := fun k => 4 * (∫ T, (Real.log (rawTreeTotal (depth k) T).toReal) ^ 2
      ∂(rawCascadeLaw (depth k) (b k) : Measure (RawTree (depth k)))) + H + 4 + C * (K + 4 * m + 8) ^ 2
    have he : ∀ᶠ k in atTop, perturbationScale (N k) ≤ 1 / 32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k) ≤ 1 / 4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hjN : ∀ᶠ k in atTop, j < N k := hNlim.eventually (eventually_gt_atTop j)
    apply squeeze_zero_norm' _ (hrate j ‖BD‖)
    filter_upwards [he, hs, hjN] with k he hs hjN
    let j' : Fin (N k) := ⟨j, hjN⟩
    have hg := hbound (N k) (hN k) (μ k) (hμinv k) m (eig k) (c k) K hK (heig k)
      (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k) (depth k) (b k) (hb k) (h k) (hh k) (h0 k) H (hH k)
      he hs (hmin k) j' q i D hD ‖BD‖ (norm_nonneg BD) hDb
    simpa only [tensorPerturbedArrayLaw, j', hj, Real.norm_eq_abs, Function.comp_def, L] using hg

end InvariantIsing

end

end OAI
