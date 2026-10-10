import OAI.Probability.InvariantIsing.Fields.SpinPriorContactContradiction
import OAI.Probability.InvariantIsing.Fields.SpinPriorContactGG

namespace OAI

/-! Compactness and the minimizing GG subsequence discharge the limiting
array assumptions in the contact contradiction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorContact_no_positive_minimizing_sequence
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (δ S H : ℝ) (hδ : 0 < δ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S
        (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) (p k) ≤
      spinPriorContactObjective (μ k) (π k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S
        (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (hpos : ∀ k, 0 < (p k).1) : False := by
  obtain ⟨Q, q, φ, hφ, hL, hgg, hd, _⟩ := spinPriorContact_minimizers_have_GG_limit hhaar hgauss
    N hN hNlim m n μ hμinv π (chainExponent cut) (chainExponent_admissible hc hfirst hlast)
    eig c K hK heig I (fun i => (cut i.succ - cut i.castSucc) * values i) S
    (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) H p hp hmin
  obtain ⟨t, _, ψ, hψ, hT⟩ := isCompact_Icc.tendsto_subseq
    (fun k => (tensorContactRegion_bounds (hp (φ k))).1)
  let τ : ℕ → ℕ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  apply spinPriorContact_limit_contradiction (fun k => N (τ k)) (fun k => by have := hN (τ k); omega)
    (hNlim.comp hτ.tendsto_atTop) m n (fun k => μ (τ k)) (fun k => hμinv (τ k)) (fun k => π (τ k))
    (fun k => eig (τ k)) (fun k => c (τ k)) K (fun k => heig (τ k))
    (fun k => I (τ k)) (fun k => hdis (τ k)) (fun k => hcover (τ k))
    lam (fun k => hlam (τ k)) ρ hρpos hρsum (hρ.comp hτ.tendsto_atTop)
    cut hc hfirst hlast trial values hvalues δ S H hδ
    (fun k => p (τ k)) (fun k => hp (τ k)) (fun k => hmin (τ k))
    (fun k => hcap (τ k)) (fun k => hpos (τ k)) t hT Q
    (hL.comp hψ.tendsto_atTop) hgg (fun a => (q a : ℝ)) (fun a => (q a).property.1) hd

end InvariantIsing

end

end OAI
