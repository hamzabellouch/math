import OAI.Analysis.KadisonKastler.CoreFrequencyVectors
import OAI.Analysis.KadisonKastler.RegularCoreFixed

namespace OAI

/-! # Bounded spectral multipliers of the common regular action

These operators lie in the core commutant. They are used to recover
frequency packets from the bounded-frequency trace vector.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def regularActionMultiplier (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  unitaryConj (star (regularGauge U hU))
    ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
      (regularScalarMultiplier φ hφ C hC))

theorem commute_regularActionMultiplier_of_fixed
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s, unitaryConj (regularCoreAction U s) T = T)
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    Commute T (regularActionMultiplier U hU φ hφ C hC) := by
  let F := Lp.fourierTransformₗᵢ ℝ H
  let T' := unitaryConj (regularGauge U hU) T
  have htrans (s : Multiplicative ℝ) : Commute T'
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    ((commute_unitary_iff_star_right_conjugate (regularRightTranslation (H := H) s).property).mpr
      (regularGauge_translation_fixed U hU hT s)).symm
  have hspec := commute_scalarMultiplier_of_characters (F.conjStarAlgEquiv T')
    (fourier_commute_characters_of_translations T' htrans) φ hφ C hC
  have hback (A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
      F.symm.conjStarAlgEquiv (F.conjStarAlgEquiv A) = A := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm,
      LinearIsometryEquiv.symm_apply_apply]
  have hspec' := hspec.map F.symm.conjStarAlgEquiv
  rw [hback] at hspec'
  have hfinal := hspec'.map (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
  change Commute (unitaryConj (star (regularGauge U hU))
      (unitaryConj (regularGauge U hU) T))
    (regularActionMultiplier U hU φ hφ C hC) at hfinal
  rwa [unitaryConj_star_unitaryConj] at hfinal

theorem regularActionMultiplier_mem_commutant (M : VonNeumannAlgebra H)
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    regularActionMultiplier U hU φ hφ C hC ∈ (regularCoreAlgebra U hU M).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact (commute_regularActionMultiplier_of_fixed U hU T
    ((mem_fixedPointAlgebra_iff _ _ _).mp
      (regularCoreAlgebra_le_fixed U hU M hM hT)).2 φ hφ C hC).eq

end

end KadisonKastler

end OAI
