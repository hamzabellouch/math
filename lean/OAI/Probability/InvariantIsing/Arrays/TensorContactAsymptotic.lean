import OAI.Probability.InvariantIsing.Arrays.TensorContactNoSequence
import OAI.Probability.InvariantIsing.Arrays.TensorContactCap
import OAI.Probability.InvariantIsing.Arrays.TensorContactZeroBoundary

namespace OAI

/-! Uniform asymptotic nonnegativity of the actual contact problem for a
fixed trial partition. Only the two named concentration inputs are assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_eventually_nonnegative
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
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
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (δ S : ℝ) (hδ : 0 < δ) (hS : entropyFunctional trial ≤ (S : EReal)) :
    ∃ H : ℝ, 0 < H ∧ ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ p ∈ tensorContactRegion (N k) m n H,
        -η ≤ tensorContactObjective (μ k) (eig k) (fun _ => 0) (I k) (chainExponent cut)
          (fun i => (cut i.succ - cut i.castSucc) * values i) S
          (fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ) p := by
  classical
  let V : ℝ → ℝ := fun t => finiteTemperatureFunctional ρ lam hρpos hρsum trial t + t * δ
  have hV : Continuous V := (continuous_finiteTemperatureFunctional ρ lam hρpos hρsum trial).add
    (continuous_id.mul continuous_const)
  have hV0 : V 0 = 0 := by simp [V, finiteTemperatureFunctional]
  obtain ⟨tmin, _, hlow⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hV.continuousOn
  obtain ⟨H, hH, hcap⟩ := exists_tensorContactObjective_cap hhaar hgauss m n cut hc hfirst hlast
    trial values hvalues d hd htrial K S (V tmin)
  refine ⟨H, hH, ?_⟩
  intro η hη
  have hcost : ∀ᶠ k in atTop,
      2 * m * perturbationScale (N k) + 8 * perturbationScale (N k) ^ 2 < η :=
    ((fullPerturbationCost_tendsto m).comp hNlim).eventually (gt_mem_nhds hη)
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ p ∈ tensorContactRegion (N k) m n H,
      tensorContactObjective (μ k) (eig k) (fun _ => 0) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V p < -η := by
    simpa only [V, Filter.not_eventually, not_forall, not_imp, not_le, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop (hbad'.and_eventually hcost)
  have hmins (k : ℕ) := tensorContactObjective_exists_minimum hhaar hgauss (hN (φ k))
    (μ (φ k)) (hμinv (φ k)) (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
    (chainExponent_admissible hc hfirst hlast) K (heig (φ k))
    (fun i => (cut i.succ - cut i.castSucc) * values i) S V hV H hH.le
  choose p hp hmin using hmins
  have hneg (k : ℕ) :
      tensorContactObjective (μ (φ k)) (eig (φ k)) (fun _ => 0) (I (φ k)) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) < -η := by
    obtain ⟨q, hq, hqneg⟩ := (hφbad k).1
    exact (hmin k q hq).trans_lt hqneg
  have hcap' (k : ℕ) : (∑ i, (p k).2.1 i) < H := by
    have hb := tensorContactRegion_bounds (hp k)
    apply hcap (N (φ k)) (hN (φ k)) (μ (φ k)) inferInstance (hμinv (φ k))
      (eig (φ k)) (I (φ k)) (heig (φ k)) V (fun t ht => hlow ht) (p k) hb.1 hb.2.1
    · intro j
      rw [abs_of_nonneg (by have := (hb.2.2.2.1 j).1; linarith)]
      exact (hb.2.2.2.1 j).2
    · intro j
      rw [abs_of_nonneg (by have := (hb.2.2.2.2 j).1; linarith)]
      exact (hb.2.2.2.2 j).2
    · linarith [hneg k]
  have hpos (k : ℕ) : 0 < (p k).1 := by
    have hb := tensorContactRegion_bounds (hp k)
    by_contra hzero
    have heq : (p k).1 = 0 := le_antisymm (not_lt.mp hzero) hb.1.1
    have hu j : |(p k).2.2.1 j| ≤ 2 := by
      rw [abs_of_nonneg (by have := (hb.2.2.2.1 j).1; linarith)]
      exact (hb.2.2.2.1 j).2
    have hv j : |(p k).2.2.2 j| ≤ 2 := by
      rw [abs_of_nonneg (by have := (hb.2.2.2.2 j).1; linarith)]
      exact (hb.2.2.2.2 j).2
    have hzeroBound := tensorContact_zero_temperature_bound hhaar hgauss (hN (φ k))
      (μ (φ k)) (hμinv (φ k)) (eig (φ k)) (I (φ k)) cut hc hfirst hlast
      (p k).2.1 hb.2.1 (p k).2.2.1 hu (p k).2.2.2 hv trial values hvalues S hS V hV0
    have hpEq : p k = (0, (p k).2.1, (p k).2.2.1, (p k).2.2.2) := by
      exact Prod.ext heq (Prod.ext rfl (Prod.ext rfl rfl))
    rw [← hpEq] at hzeroBound
    have := (hφbad k).2
    linarith [hneg k]
  exact tensorContact_no_positive_minimizing_sequence hhaar hgauss
    (fun k => N (φ k)) (fun k => hN (φ k)) (hNlim.comp hφ.tendsto_atTop) m n
    (fun k => μ (φ k)) (fun k => hμinv (φ k)) (fun k => eig (φ k)) (fun _ _ => 0)
    K hK (fun k => heig (φ k)) (fun k => I (φ k)) (fun k => hdis (φ k))
    (fun k => hcover (φ k)) lam (fun k => hlam (φ k)) ρ hρpos hρsum
    (hρ.comp hφ.tendsto_atTop) cut hc hfirst hlast trial values hvalues δ S H hδ p hp hmin hcap' hpos

end InvariantIsing

end

end OAI
