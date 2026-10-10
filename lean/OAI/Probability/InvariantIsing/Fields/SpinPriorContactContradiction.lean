import OAI.Probability.InvariantIsing.Fields.SpinPriorContactTailOrder
import OAI.Probability.InvariantIsing.Fields.SpinPriorContactTemperature
import OAI.Probability.InvariantIsing.Arrays.TensorSingleObservable
import OAI.Probability.InvariantIsing.Fields.SpinPriorEnergyLimit
import OAI.Probability.InvariantIsing.Spectral.SpectralContactContradiction

namespace OAI

/-! At an actual positive-temperature contact minimum, the field directions
and temperature direction contradict the identified limiting energy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem spinPriorContact_limit_contradiction
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (π : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (π k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (heig : ∀ k i, |eig k i| ≤ K)
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
    (hpos : ∀ k, 0 < (p k).1)
    (t : ℝ) (ht : Tendsto (fun k => (p k).1) atTop (𝓝 t))
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => spinPriorPerturbedArrayLaw (n := n) (μ k) (π k) (chainExponent cut) (eig k) (c k) (I k)
      (p k).2.2.1 (p k).2.2.2 (p k).1 (finiteFieldPath (p k).2.1))
      atTop (𝓝 Q))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a) : False := by
  have ht0 : 0 ≤ t := ge_of_tendsto' ht (fun k => (hpos k).le)
  have hh k := monotone_finiteFieldPath (tensorContactRegion_bounds (hp k)).2.1
  have h0 k := finiteFieldPath_nonneg (tensorContactRegion_bounds (hp k)).2.1 0
  have hu k j : |(p k).2.2.1 j| ≤ 2 := by
    have h := (tensorContactRegion_bounds (hp k)).2.2.2.1 j
    rw [abs_of_nonneg (by linarith [h.1] : 0 ≤ (p k).2.2.1 j)]
    exact h.2
  have hv k a : |(p k).2.2.2 a| ≤ 2 := by
    have h := (tensorContactRegion_bounds (hp k)).2.2.2.2 a
    rw [abs_of_nonneg (by linarith [h.1] : 0 ≤ (p k).2.2.2 a)]
    exact h.2
  obtain ⟨hP, hn, henergy⟩ := spinPriorPerturbedArrayLaw_interactionEnergy_limit N hN hNlim m n
    μ hμinv π (chainExponent cut) eig c I hdis hcover lam hlam
    (fun k => (p k).2.2.1) hu (fun k => (p k).2.2.2) hv
    (fun k => (p k).1) ht (fun k => finiteFieldPath (p k).2.1)
    hh h0 Q hL ρ hρpos hρsum hρ hgg q hq hd ht0
  have htail := spinPriorContact_limit_tail_order N hN m n μ π eig c I hdis hcover
    cut hc hfirst hlast trial values hvalues S
    (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ)
    H p hp hmin hcap Q hL hgg q hq hd hP hn
  apply spectralContact_contradiction ρ lam hρpos hρsum
    (spectralSpinQuantilePath Q hP hn) trial hδ ht0 (fun k => (p k).1) _ ht henergy _ htail
  apply Filter.Eventually.of_forall
  intro k
  have he := spinPriorContact_minimum_energy_gap (hN k) (μ k) (π k) (chainExponent cut) (eig k) (c k) (I k)
    (fun i => (cut i.succ - cut i.castSucc) * values i)
    ρ lam hρpos hρsum trial δ S H (p k) (hp k) (hmin k) (hpos k) K (heig k)
  exact he

end InvariantIsing

end

end OAI
