import OAI.GroupTheory.Thompson.MeanApproximation
import OAI.GroupTheory.Thompson.FiniteCoarea

namespace OAI

noncomputable section

open scoped BigOperators symmDiff

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

/-- A standard invariant mean yields a finite set with small total boundary. -/
theorem InvariantMean.exists_folner_total (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * A.card := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  obtain ⟨p, hp, hsmall⟩ := M.exists_probability_small_defect S hε
  have hmass : ∑ g ∈ p.support, p g = 1 := by
    simpa only [mass_apply] using hp.2
  have hdef : (∑ h ∈ S, ∑ x ∈ p.support ∪ leftTranslate h p.support,
      |p (h⁻¹ * x) - p x|) < ε := by
    simpa only [norm_defectMap, leftTranslate] using hsmall
  exact finite_folner_of_small_defect (p := fun g => p g) (K := p.support)
    (S := S) hp.1 (fun g hg => Finsupp.notMem_support_iff.mp hg) hmass hdef

/-- Finite Følner sets, with no countability or finite-generation assumption. -/
theorem InvariantMean.exists_folner (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      ∀ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ) < ε * A.card := by
  obtain ⟨A, hA, htotal⟩ := M.exists_folner_total S hε
  refine ⟨A, hA, ?_⟩
  intro h hh
  have hone : ((leftTranslate h A ∆ A).card : ℝ) ≤
      ∑ g ∈ S, ((leftTranslate g A ∆ A).card : ℝ) :=
    Finset.single_le_sum (f := fun g => ((leftTranslate g A ∆ A).card : ℝ))
      (fun g _ => Nat.cast_nonneg _) hh
  exact hone.trans_lt htotal

/-- Uniform expansion of nonempty finite sets rules out a standard invariant mean. -/
theorem not_amenable_of_uniform_boundary (S : Finset G) {b : ℝ} (hb : 0 < b)
    (hexpand : ∀ A : Finset G, A.Nonempty →
      ∃ h ∈ S, b * A.card ≤ ((leftTranslate h A ∆ A).card : ℝ)) :
    ¬ Nonempty (InvariantMean G) := by
  rintro ⟨M⟩
  obtain ⟨A, hA, hsmall⟩ := M.exists_folner S hb
  obtain ⟨h, hh, hlarge⟩ := hexpand A hA
  exact not_le_of_gt (hsmall h hh) hlarge

end ThompsonNonamenability

end

end OAI
