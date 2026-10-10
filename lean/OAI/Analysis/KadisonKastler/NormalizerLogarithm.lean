import OAI.Analysis.KadisonKastler.ExponentialCommutator
import OAI.Analysis.KadisonKastler.Normalizer
import OAI.Analysis.KadisonKastler.UnitaryLogarithmBound

namespace OAI

/-! # The logarithm of a small normalizer preserves the algebra

The bounded operators preserving a closed linear subspace form a closed
subalgebra. Uniform exponential inversion recovers the commutator generator
inside that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded maps on the ambient operator algebra preserving `P`. -/
def preservingOperatorAlgebra (P : VonNeumannAlgebra H) :
    Subalgebra ℂ ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) where
  carrier := {T | ∀ a ∈ P, T a ∈ P}
  zero_mem' := by intro a ha; exact P.zero_mem
  one_mem' := by intro a ha; exact ha
  add_mem' := by intro T U hT hU a ha; exact P.add_mem (hT a ha) (hU a ha)
  mul_mem' := by intro T U hT hU a ha; exact hT _ (hU a ha)
  algebraMap_mem' := by
    intro c a ha
    change c • a ∈ P
    exact P.smul_mem ha c

theorem preservingOperatorAlgebra_isClosed (P : VonNeumannAlgebra H) :
    IsClosed (preservingOperatorAlgebra P :
      Set ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))) := by
  have he : (preservingOperatorAlgebra P : Set ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))) =
      ⋂ a : Algebra P, {T | T (a : H →L[ℂ] H) ∈ P} := by
    ext T
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h a => h a a.property, fun h a ha => h ⟨a, ha⟩⟩
  rw [he]
  exact isClosed_iInter fun a => (isClosed_algebra P).preimage
    ((ContinuousLinearMap.apply ℂ (H →L[ℂ] H) a.val).continuous)

/-- In the absolute logarithm radius, conjugation invariance implies
invariance under the bounded commutator. -/
theorem commutator_mem_of_small_expUnitary_normalizes
    (P : VonNeumannAlgebra H) (h : selfAdjoint (H →L[ℂ] H))
    (hsmall : ‖(h : H →L[ℂ] H)‖ ≤ 1 / 32)
    (hnormalizes : Conjugates (H := H) (selfAdjoint.expUnitary h) P P) :
    ∀ a ∈ P, (h : H →L[ℂ] H) * a - a * (h : H →L[ℂ] H) ∈ P := by
  let D := boundedCommutator (Complex.I • (h : H →L[ℂ] H))
  have hDnorm : ‖D‖ ≤ 1 / 16 := by
    have hn := norm_boundedCommutator_le (Complex.I • (h : H →L[ℂ] H))
    simp only [norm_smul, Complex.norm_I, one_mul] at hn
    exact hn.trans (by linarith)
  have hexp : NormedSpace.exp D ∈ preservingOperatorAlgebra P := by
    intro a ha
    rw [exp_boundedCommutator_apply]
    have hn := hnormalizes
    change unitaryConj (H := H) (selfAdjoint.expUnitary h) '' (P : Set (H →L[ℂ] H)) =
      (P : Set (H →L[ℂ] H)) at hn
    have hm : unitaryConj (H := H) (selfAdjoint.expUnitary h) a ∈ P := by
      change unitaryConj (H := H) (selfAdjoint.expUnitary h) a ∈ (P : Set (H →L[ℂ] H))
      rw [← hn]
      exact ⟨a, ha, rfl⟩
    convert hm using 1
    simp only [unitaryConj, selfAdjoint.expUnitary_coe, NormedSpace.star_exp,
      star_smul, Complex.star_def, Complex.conj_I, h.property.star_eq, neg_smul]
  have hD := mem_closedSubalgebra_of_exp_mem (preservingOperatorAlgebra P)
    (preservingOperatorAlgebra_isClosed P) D hDnorm hexp
  intro a ha
  have hi := P.smul_mem (hD a ha) (-Complex.I)
  change (-Complex.I) • ((Complex.I • (h : H →L[ℂ] H)) * a -
    a * (Complex.I • (h : H →L[ℂ] H))) ∈ P at hi
  simpa only [smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    neg_mul, Complex.I_mul_I, neg_neg, one_smul] using hi

/-- The controlled principal logarithm of a sufficiently small exact
normalizer implements a derivation of the algebra. -/
theorem exists_small_normalizer_log (P : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates (H := H) v P P)
    (hsmall : ‖(v : H →L[ℂ] H) - 1‖ < 1 / 64) :
    ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = v ∧
      ‖(h : H →L[ℂ] H)‖ ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ ∧
      ∀ a ∈ P, (h : H →L[ℂ] H) * a - a * (h : H →L[ℂ] H) ∈ P := by
  obtain ⟨h, hh, hn⟩ := exists_small_selfAdjoint_log v (by linarith)
  refine ⟨h, hh, hn, ?_⟩
  apply commutator_mem_of_small_expUnitary_normalizes P h
  · exact hn.trans (by linarith)
  · rwa [hh]

end

end KadisonKastler

end OAI
