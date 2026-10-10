import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryGuesses

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Guided Comparison
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

noncomputable abbrev RecoveryIndex (D F : Finset V) (Δ : ℝ) (L U n : ℕ) :=
  Σ guess : RecoveryGuesses L U, Fin n ×
    ((Fin (2*guess.1.val) × Fin (integralPrecision D Δ guess.1.val)) ⊕
      Fin (localTapeBound F guess.1.val))

noncomputable def recoveryRawEquiv (D F : Finset V) (Δ : ℝ) (L U n : ℕ) :
    (RecoveryIndex D F Δ L U n → Bool) ≃ RecoverySeed D F Δ L U n :=
  (Equiv.piCurry (fun _ _ => Bool)).trans
    (Equiv.piCongrRight (fun _guess =>
      (Equiv.curry (Fin n) _ Bool).trans (Equiv.piCongrRight (fun _ =>
        (Equiv.sumArrowEquivProdArrow _ _ Bool).trans
          (Equiv.prodCongr (Equiv.curry _ _ Bool) (Equiv.refl _))))))

noncomputable def recoveryBitCount (D F : Finset V) (Δ : ℝ) (L U n : ℕ) : ℕ :=
  Fintype.card (RecoveryIndex D F Δ L U n)

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma recoveryBitCount_eq (D F : Finset V) (Δ : ℝ) (L U n : ℕ) :
    recoveryBitCount D F Δ L U n =
      ∑ guess : RecoveryGuesses L U,
        n * (2*guess.1.val * integralPrecision D Δ guess.1.val + localTapeBound F guess.1.val) := by
  simp only [recoveryBitCount,RecoveryIndex,Fintype.card_sigma,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_sum]

noncomputable def recoveryTapeEquiv (D F : Finset V) (Δ : ℝ) (L U n : ℕ) :
    (Fin (recoveryBitCount D F Δ L U n) → Bool) ≃ RecoverySeed D F Δ L U n :=
  ((Fintype.equivFin (RecoveryIndex D F Δ L U n)).symm.arrowCongr (Equiv.refl Bool)).trans
    (recoveryRawEquiv D F Δ L U n)

end MetricKMedianRecovery.Sampling

end OAI
