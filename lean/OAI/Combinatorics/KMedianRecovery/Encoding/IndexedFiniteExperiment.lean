import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DisjointFiniteExperiment
import OAI.Combinatorics.KMedianRecovery.Geometry.OptimumMinCard
import OAI.Combinatorics.KMedianRecovery.Recovery.Order

namespace OAI

namespace MetricKMedianRecovery.RoundedAssembly
open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies

theorem indexed_finite_experiment : ∃ v : ℚ, 0 < v ∧ ∃ Nstar : ℕ, 1 ≤ Nstar ∧
    ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [PseudoMetricSpace V] [LinearOrder V] [Fintype V],
    ∀ (F D : Finset V) (k : ℕ) (ζ : ℝ),
    F.Nonempty → 0 < k → 0 < ζ →
    let C := Rounding.cap D.card (gamma/16)
    let L0 := countBound (commonL v Nstar D.card C)
    let n := repetitions c L0 ζ
    ∃ run : RecoverySeed (marked false D) (marked true F) C L0 (D.card*C) n → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k ∧
        cost D (run seed) ≤ 6*optimum F D k) ∧
      1-ζ ≤ probability (fun seed => cost D (run seed) ≤ (2-gamma/2)*optimum F D k) ∧
      average (fun seed => cost D (run seed)) ≤
        ((2-gamma/2)+6*ζ)*optimum F D k := by
  classical
  obtain ⟨v,hv,Nstar,hNstar,c,hc,H⟩ := disjoint_finite_experiment
  refine ⟨v,hv,Nstar,hNstar,c,hc,?_⟩
  intro V instMetric instOrder instFinite F D k ζ hF hk hζ
  let C := Rounding.cap D.card (gamma/16)
  let L0 := countBound (commonL v Nstar D.card C)
  let n := repetitions c L0 ζ
  let Ω := RecoverySeed (marked false D) (marked true F) C L0 (D.card*C) n
  by_cases hD : D.Nonempty
  · have hk' : 0 < min k F.card := lt_min hk hF.card_pos
    have hkF' : min k F.card ≤ (marked true F).card := by
      simpa only [marked_card] using min_le_right k F.card
    have hcall := @H (V × Bool) metric (order V) (inferInstance)
      (marked true F) (marked false D) (min k F.card) ζ
      ((marked_nonempty false D).mpr hD) hk' hkF' (marked_disjoint D F) hζ
    dsimp only at hcall
    rw [marked_card false D] at hcall
    obtain ⟨run,hfeas,hprob,hexp⟩ := hcall
    have hproject (seed : Ω) := project_set F (run seed) (hfeas seed).1
    let out (seed : Ω) : Finset V := Classical.choose (hproject seed)
    have hout (seed : Ω) := Classical.choose_spec (hproject seed)
    have heq (seed : Ω) : @cost (V × Bool) metric (marked false D) (run seed) = cost D (out seed) := by
      rw [←(hout seed).2.1,cost_marked]
    have hopteq : @optimum (V × Bool) metric (marked true F) (marked false D) (min k F.card) =
        optimum F D k := by
      rw [optimum_marked F D hF _ hk',optimum_min_card]
    refine ⟨out,?_,?_,?_⟩
    · intro seed
      refine ⟨(hout seed).1,?_,?_,?_⟩
      · exact (marked_nonempty true (out seed)).mp ((hout seed).2.1.symm ▸ (hfeas seed).2.1)
      · exact (hout seed).2.2.trans_le ((hfeas seed).2.2.1.trans (min_le_left _ _))
      · simpa only [heq,hopteq] using (hfeas seed).2.2.2
    · simpa only [heq,hopteq] using hprob
    · simpa only [heq,hopteq] using hexp
  · have hDe : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    have hcost (S : Finset V) : cost D S = 0 := by simp only [hDe,cost,Finset.sum_empty]
    obtain ⟨f,hf⟩ := hF
    have hopt : optimum F D k = 0 := le_antisymm
      ((optimum_le F D {f} k (Finset.singleton_subset_iff.mpr hf) (Finset.singleton_nonempty _)
        (by simpa only [Finset.card_singleton] using Nat.succ_le_iff.mpr hk)).trans_eq (hcost _))
      (optimum_nonneg F D k)
    refine ⟨fun _ => {f},fun _ => ⟨Finset.singleton_subset_iff.mpr hf,
      Finset.singleton_nonempty _,by simpa only [Finset.card_singleton] using Nat.succ_le_iff.mpr hk,?_⟩,?_,?_⟩
    · rw [hcost,hopt]; norm_num
    · simp only [hcost,hopt,mul_zero,le_refl,probability,ite_true,average_const]
      linarith
    · simp only [hcost,hopt,mul_zero,average_const,le_refl]

end MetricKMedianRecovery.RoundedAssembly

end OAI
