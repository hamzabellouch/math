import OAI.NumberTheory.Ostmann.Construction.CollisionBalancedPrior
import OAI.NumberTheory.Ostmann.Construction.WholeShellRetainedLinearMass
import OAI.NumberTheory.Ostmann.Construction.SelectedCellGap
import OAI.NumberTheory.Ostmann.Construction.TailFourierMass

namespace OAI

/-! # The original broad bulk prior has balanced mass at least one half -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_broad_prior_balance
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ Y : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let Q := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      ∀ P : Finset ℕ, Q ⊆ P →
      (1 / 2 : ℝ) ≤ ∑ p : P,
        if (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3
        then primeSubsetPrior P Q p else 0 := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hlarge.and (eventual_tailCollisionCutoff N))
  have ht (b : ℝ) (hb : 0 < b) : Tendsto (fun L : ℝ => Real.exp (b * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  refine ⟨a, ha, ?_⟩
  filter_upwards [whole_shell_retained_linear_mass hM 1 (by norm_num),
    eventual_tail_cell_window a C 0,
    (ht (4 / 100) (by norm_num)).eventually (eventually_ge_atTop Y₀),
    (ht (4 / 1000) (by norm_num)).eventually
      (eventually_ge_atTop (128000 * tailCellLinearRate a C)),
    eventually_ge_atTop (1 : ℝ)] with L hmass hwindow hlargeY hratio hL
  intro Y hYlo hYhi hi hhi D hD Q P hQP
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYlo
  obtain ⟨hlarge, hcut⟩ := hY₀ Y (hlargeY.trans hYlo)
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge hi hhi
  let ambient := Nat.primesLE (tailCollisionCutoff Y)
  let S := tailSupport A N
  let T := fun p => Finset.range p \ S p
  let μ := fun p => residueMass (summandTail A (summandTailCutoff Y) hi)
    (fun _ => 1 / ((summandTail A (summandTailCutoff Y) hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B (summandTailCutoff Y) hi)
    (fun _ => 1 / ((summandTail B (summandTailCutoff Y) hi).card : ℝ)) (negativeResidue p)
  have hprime (p) (hp : p ∈ ambient) := Nat.prime_of_mem_primesLE hp
  have hS (p) (hp : p ∈ ambient) : (S p).Nonempty := tailSupport_nonempty hA N p (hprime p hp).pos
  have hT (p) (hp : p ∈ ambient) : (T p).Nonempty :=
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard (p) : (S p).card + (T p).card = p := tailSupport_card_add_complement A N p
  have hnon (p) (hp : p ∈ ambient) : 0 ≤ Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) :=
    mul_nonneg (Real.log_natCast_nonneg p) (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p).le)
  have hbudget : (∑ p ∈ ambient, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤
      tailDefectBudget a C Y := by
    apply uniform_tail_collision_bound hA hB N (summandTailCutoff Y) hi a Y C ha
      hcut.1 hcut.2.1 hhi hcut.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    · simpa only [positiveSummandTail_card] using hsa
    · simpa only [negativeSummandTail_card] using hsb
    · exact hM.lower
  have hD0 : 0 ≤ tailDefectBudget a C Y := (Finset.sum_nonneg hnon).trans hbudget
  obtain ⟨_, hcellcut, _⟩ := hwindow Y (Real.exp ((1 / 100 : ℝ) * L)) hYlo hYhi le_rfl
    (Real.exp_le_exp.mpr (by linarith))
  have hQA : Q ⊆ ambient := by
    intro p hp
    obtain ⟨hpp, _, _, hupper⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    have hlog : Real.log (p : ℝ) ≤ Real.log (tailCollisionCutoff Y : ℝ) := by
      have hh : Real.exp ((6 / 1000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hQpos : (0 : ℝ) < tailCollisionCutoff Y := by
      exact_mod_cast (tailCollisionCutoff_bounds Y hcut.1 hcut.2.1).1
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast (Real.log_le_log_iff
      (by exact_mod_cast hpp.pos) hQpos).mp hlog, hpp⟩
  have hMQ : L / 16000 ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ := hmass D (by simpa only [one_mul] using hD)
  have hsmall : 4 * tailDefectBudget a C Y / Real.exp ((4 / 1000 : ℝ) * L) ≤
      (∑ p ∈ Q, (p : ℝ)⁻¹) / 2 := by
    have hb := tailDefectBudget_linear a C L Y hL hYp hYhi
    have hK := tailCellLinearRate_nonneg a C
    have hprod := mul_le_mul_of_nonneg_right hratio (show 0 ≤ L by linarith)
    apply le_trans _ (show L / 32000 ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) / 2 by linarith)
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  have hbal := collision_harmonic_prior_balanced_mass P Q Q hQP (fun _ hp => hp) S T μ ν
    (tailDefectBudget a C Y) (Real.exp ((4 / 1000 : ℝ) * L)) (Real.exp_pos _)
    (fun p hp => hprime p (hQA hp)) (fun p hp => hS p (hQA hp)) (fun p hp => hT p (hQA hp))
    (fun p _ => hcard p)
    (fun p hp => (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1).2.2.1.le)
    ((Finset.sum_le_sum_of_subset_of_nonneg hQA (fun p hp _ => hnon p hp)).trans hbudget)
    ((by linarith : 0 < L / 16000).trans_le hMQ) hsmall
  have he (p : P) := tailDensityMask_balanced_iff A N p
  apply hbal.trans_eq
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (p : ℕ) ∈ Q
  · have hb := (he p (hprime p (hQA hp)).pos)
    simp only [hb, S]
  · have hz : primeSubsetPrior P Q p = 0 := by simp only [primeSubsetPrior, hp, ite_false]
    simp only [hz, ite_self]

end Ostmann

end OAI
