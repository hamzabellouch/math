import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeAdaptedMaximalBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SectionWeightedBoxes

namespace OAI

/-! # Uniform bracket bounds in actual ideal and pure-section coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Set

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- The pure quotient words completing a maximal ideal basis give an
adapted basis with uniformly bounded rescaled bracket coefficients. -/
theorem exists_cone_section_basis_bound
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C bI s β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (q : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        FreeMagma (Fin M.letterCount)),
      (∀ j, ¬IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (q j)) ∧
      ∃ hq : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ
        (evalBracketWord M.letter (q j)) = bQ j,
      ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 ≤ r →
        let B := exponentialRescaleBasis
          (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
            (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
            bQ (fun j => evalBracketWord M.letter (q j)) hq)
          (Sum.elim (fun j => M.coneIdealWordCost C s (β.val j)) (fun _ => 0)) r
        ∀ i j k, |B.repr ⁅B i, B j⁆ k| ≤ A := by
  obtain ⟨bQ, q, hpure, hq, e, γ, hγ, hcost, hmax, _⟩ :=
    M.exists_cone_adapted_maximal_basis_data C bN bI s hs hzero β hβ
  obtain ⟨A, hA, hbound⟩ := exists_uniform_rescaled_structureConstant_bound
    M.letter M.bound_zero bN
  refine ⟨bQ, q, hpure, hq, A, hA, ?_⟩
  intro r hr
  dsimp only
  let B := basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    bQ (fun j => evalBracketWord M.letter (q j)) hq
  let cost : (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
      Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))) → ℝ :=
    Sum.elim (fun j => M.coneIdealWordCost C s (β.val j)) (fun _ => 0)
  have heq : exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun k => bracketWordExponent s (γ.val k)) r =
      (exponentialRescaleBasis B cost r).reindex e := by
    rw [hγ]
    simp_rw [hcost]
    exact exponentialRescaleBasis_reindex B cost e r
  intro i j k
  have hh := hbound s γ hmax r hr (e i) (e j) (e k)
  rw [heq] at hh
  simpa only [Basis.reindex_apply, Basis.repr_reindex_apply, Equiv.symm_apply_apply] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
