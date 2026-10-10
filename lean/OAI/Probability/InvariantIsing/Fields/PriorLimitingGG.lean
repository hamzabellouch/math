import OAI.Probability.InvariantIsing.Fields.PriorArrayResidualBound
import OAI.Probability.InvariantIsing.Arrays.TensorLimitingGG

namespace OAI

/-! Vector GG identities in weak limits of actual constrained-prior minimizers. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

def priorPerturbedArrayLaw {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  priorNamespacedArrayLaw μ ν (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    (fun j : Fin N => enumeratedTreeDegree m j) h

theorem priorPerturbation_minimizers_spectralGG
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
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) := by
  obtain ⟨C,hC,hbound⟩ := priorPerturbation_arrayResidual_bound hhaar hgauss
  apply spectralGG_of_weak_nonconstant_monomial_residuals hL
  intro z hz i D hD d hd
  cases z with
  | zero => omega
  | succ q =>
    obtain ⟨j,hj⟩ := enumeratedJointMonomial_surjective m d hd
    let BD := BoundedContinuousFunction.mkOfCompact ⟨D,hD⟩
    have hDb : ∀ x, |D x|≤‖BD‖ := fun x => by
      simpa only [BD,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,Real.norm_eq_abs]
        using BD.norm_coe_le_norm x
    let L := H+4+C*(K+4*m+8)^2
    have he : ∀ᶠ k in atTop, perturbationScale (N k)≤1/32 :=
      (perturbationScale_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hs : ∀ᶠ k in atTop, contactStep (N k)≤1/4 :=
      (contactStep_tendsto.comp hNlim).eventually (eventually_le_nhds (by norm_num))
    have hjN : ∀ᶠ k in atTop, j<N k := hNlim.eventually (eventually_gt_atTop j)
    apply squeeze_zero_norm' _ ((tensorContactGGRate_tendsto j m L ‖BD‖).comp hNlim)
    filter_upwards [he,hs,hjN] with k he hs hjN
    let j' : Fin (N k) := ⟨j,hjN⟩
    have hg := hbound (N k) (hN k) (μ k) (hμinv k) m n (ν k)
      (eig k) (c k) K hK (heig k) (I k) (u k) (hu k) (v k) (hv k) (t k) (ht k)
      (h k) (hh k) (h0 k) H (hH k) he hs (hmin k) j' q i D hD ‖BD‖ (norm_nonneg BD) hDb
    simpa only [priorPerturbedArrayLaw,j',hj,Real.norm_eq_abs,Function.comp_def,L] using hg

end InvariantIsing

end

end OAI
