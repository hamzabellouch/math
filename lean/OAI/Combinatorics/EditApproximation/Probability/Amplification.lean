import Mathlib

namespace OAI

/-!
# Independent-copy amplification for the seed passes

The tail estimate is the direct finite-subset argument from Section 8.
Independence is used only between copies at a fixed state. The subsequent
union bound over states makes no independence assumption between states.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

theorem independent_failure_subset_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ι → Set Ω)
    (hindep : iIndepSet bad μ) (copies : Finset ι) (q : ℝ)
    (hbad : ∀ i ∈ copies, μ.real (bad i) ≤ q) :
    μ.real (⋂ i ∈ copies, bad i) ≤ q ^ copies.card := by
  rw [measureReal_def, hindep.meas_biInter, ENNReal.toReal_prod]
  have hprod := Finset.prod_le_prod₀ (fun i _ => measureReal_nonneg) hbad
  simpa only [prod_const, measureReal_def] using hprod

theorem independent_failure_count_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ι → Set Ω)
    (hindep : iIndepSet bad μ) (k : ℕ) (q : ℝ)
    (hbad : ∀ i, μ.real (bad i) ≤ q) :
    μ.real {ω | k ≤ (univ.filter fun i => ω ∈ bad i).card} ≤
      (Fintype.card ι).choose k * q ^ k := by
  classical
  let subsets := (univ : Finset ι).powersetCard k
  have hcover : {ω | k ≤ (univ.filter fun i => ω ∈ bad i).card} ⊆
      ⋃ s ∈ subsets, ⋂ i ∈ s, bad i := by
    intro ω hω
    obtain ⟨s, hsub, hcard⟩ := exists_subset_card_eq hω
    have hs : s ∈ subsets := mem_powersetCard.mpr
      ⟨fun i hi => mem_univ i, hcard⟩
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨hs, ?_⟩⟩
    exact Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi => (mem_filter.mp (hsub hi)).2
  apply (measureReal_mono (μ := μ) hcover (measure_ne_top μ _)).trans
  apply (measureReal_biUnion_finset_le subsets _).trans
  have hbound (s : Finset ι) (hs : s ∈ subsets) :
      μ.real (⋂ i ∈ s, bad i) ≤ q ^ k := by
    have hcard := (mem_powersetCard.mp hs).2
    simpa only [hcard] using independent_failure_subset_bound μ bad hindep s q (fun i _ => hbad i)
  have hsum := sum_le_sum hbound
  simpa only [sum_const, nsmul_eq_mul, subsets, card_powersetCard, card_univ] using hsum

theorem independent_failure_count_binary_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ι → Set Ω)
    (hindep : iIndepSet bad μ) (k : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hbad : ∀ i, μ.real (bad i) ≤ q) :
    μ.real {ω | k ≤ (univ.filter fun i => ω ∈ bad i).card} ≤
      (2 : ℝ) ^ Fintype.card ι * q ^ k := by
  apply (independent_failure_count_bound μ bad hindep k q hbad).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq k)
  exact_mod_cast Nat.choose_le_two_pow (Fintype.card ι) k

end EditApproximation

end OAI
