import OAI.Probability.InvariantIsing.Fields.PriorArrayWard
import OAI.Probability.InvariantIsing.Fields.PriorArrayDiagonalWard
import OAI.Probability.InvariantIsing.Fields.PriorLimitingGG
import OAI.Probability.InvariantIsing.Spectral.SpectralPerturbedBlocks

namespace OAI

/-! Both Ward equations for weak limits of the actual fixed-prior model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem priorPerturbedArrayLaw_ward_limits
    (N : ℕ → ℕ) (hN : ∀ k, 0<N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (ν : (k : ℕ) → Measure (Spin (N k) × LabeledLeaf n)) [∀ k, IsProbabilityMeasure (ν k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k)=Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i∈I k a → eig k i=lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j|≤2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a|≤2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0≤h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m+1)))
    (hL : Tendsto (fun k => priorPerturbedArrayLaw (μ k) (ν k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ)/N k) atTop (𝓝 ρ)) :
    (∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
      spectralOffWardResidual Q ρ (fun a => t₀*lam a) a b Φ=0) ∧
    (∀ a b, spectralDiagonalWardResidual Q ρ (fun a => t₀*lam a) a b=0) := by
  let E := fun k => diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)
  let κ := fun k a => t k*lam a+2*perturbationScale (N k)*v k a
  have hκ : ∀ k a i, i∈I k a → E k i=κ k a := fun k =>
    diagonalPerturbedEigenvalues_block (eig k) (I k) (hdis k) (v k) (t k) lam (hlam k)
  have hκlim : Tendsto κ atTop (𝓝 (fun a => t₀*lam a)) :=
    perturbedBlockEigenvalues_tendsto N hNlim v hv t ht lam
  have hdegree (k : ℕ) (j : Fin (N k)) :
      (∑ a, (enumeratedSpectralDegree m j a : ℝ))≤1*((j : ℝ)+1) := by
    simpa only [one_mul] using enumeratedSpectralDegree_real_sum_le m j
  refine ⟨?_,?_⟩
  · intro a b Φ hΦ B hB hΦB
    by_cases hab : a=b
    · subst b
      simp [spectralOffWardResidual]
    have he : Tendsto (fun k => 192*B*1*perturbationScale (N k)^2) atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero] using
        (tendsto_const_nhds.mul ((perturbationScale_tendsto.comp hNlim).pow 2) :
          Tendsto (fun k => 192*B*1*perturbationScale (N k)^2) atTop (𝓝 (192*B*1*0^2)))
    apply spectralOffWardResidual_zero_of_vanishing_bound hL hρ hκlim a b Φ hΦ he
    intro k
    let := hμinv k
    exact priorNamespacedArrayLaw_off_ward_bound (hN k) (μ k) (ν k) (E k) (c k) (I k)
      (hdis k) (hcover k) (fun j => enumeratedSpectralDegree m j)
      (fun j => enumeratedTreeDegree m j) (u k) (hu k) 1 zero_le_one (hdegree k)
      (h k) (hh k) (h0 k) (κ k) a b
      (hdis k (Set.mem_univ a) (Set.mem_univ b) hab) (hκ k a) (hκ k b) Φ hΦ B hB hΦB
  · intro a b
    by_cases hab : a=b
    · subst b
      simp [spectralDiagonalWardResidual]
    have he : Tendsto (fun k => 48*1*perturbationScale (N k)^2) atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero] using
        (tendsto_const_nhds.mul ((perturbationScale_tendsto.comp hNlim).pow 2) :
          Tendsto (fun k => 48*1*perturbationScale (N k)^2) atTop (𝓝 (48*1*0^2)))
    apply spectralDiagonalWardResidual_zero_of_vanishing_bound hL hρ hκlim a b he
    intro k
    let := hμinv k
    exact priorNamespacedArrayLaw_diagonalWard_bound (hN k) (μ k) (ν k) (E k) (c k) (I k)
      (fun j => enumeratedSpectralDegree m j) (fun j => enumeratedTreeDegree m j)
      (u k) (hu k) 1 zero_le_one (hdegree k) (h k) (hh k) (h0 k) (κ k) a b
      (hdis k (Set.mem_univ a) (Set.mem_univ b) hab) (hκ k a) (hκ k b)

end InvariantIsing

end

end OAI
