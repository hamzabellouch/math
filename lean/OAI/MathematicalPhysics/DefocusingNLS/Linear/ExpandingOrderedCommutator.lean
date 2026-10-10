import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusOrderedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyInner
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLinearization

namespace OAI

/-! # Exact principal and commutator splitting of the torus linearization

The remainder below is formed from the actual odd-power derivative and
the actual physical Fourier derivative components.  Its definition adds
no spectral or compactness assumption.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance expandingOrderedCommutatorMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance expandingOrderedCommutatorProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def expandingLinearizedPotential (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (q : FourierL2) :
    FourierL2 →L[ℝ] FourierL2 :=
  (-Complex.I) • fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q

noncomputable def expandingOrderedCommutator (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ M)
    (j : Fin N → Fin 12) : FourierL2 →L[ℝ] Lp ℂ 2 (volume : Measure T) :=
  ((expandingOrderedPhysicalEnergy a L N hL j).restrictScalars ℝ).comp
      (expandingLinearizedPotential a N L ha ha1 hN hL m q) -
    (torusPrincipalPotential m (expandingUnitTorusFunction a N L q)
      (expandingUnitTorusFunction a N L q).continuous M hM hQB).comp
        ((expandingOrderedPhysicalEnergy a L N hL j).restrictScalars ℝ)

theorem expandingOrderedCommutator_split (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ M)
    (j : Fin N → Fin 12) (f : FourierL2) :
    expandingOrderedPhysicalEnergy a L N hL j
        (expandingLinearizedPotential a N L ha ha1 hN hL m q f) =
      torusPrincipalPotential m (expandingUnitTorusFunction a N L q)
        (expandingUnitTorusFunction a N L q).continuous M hM hQB
        (expandingOrderedPhysicalEnergy a L N hL j f) +
      expandingOrderedCommutator a L N ha ha1 hN hL m q M hM hQB j f := by
  simp only [expandingOrderedCommutator, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  abel

theorem expandingLinearized_energy_split (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ M)
    (f : FourierL2) :
    let B := expandingLinearizedPotential a N L ha ha1 hN hL m q
    let D := expandingOrderedPhysicalEnergy a L N hL
    let P := torusPrincipalPotential m (expandingUnitTorusFunction a N L q)
      (expandingUnitTorusFunction a N L q).continuous M hM hQB
    inner ℝ f (B f) =
      inner ℝ (expandingLowEnergy a N L hL f) (expandingLowEnergy a N L hL (B f)) +
        (∑ j, inner ℝ (D j f) (P (D j f))) +
        ∑ j, inner ℝ (D j f) (expandingOrderedCommutator a L N ha ha1 hN hL m q M hM hQB j f) := by
  intro B D P
  dsimp only [B, D, P]
  rw [expandingEnergy_inner a N L hL f (B f),
    ← expandingOrderedPhysicalEnergy_inner a L N hL f (B f)]
  simp only [B, expandingOrderedCommutator_split a L N ha ha1 hN hL m q M hM hQB,
    inner_add_right, Finset.sum_add_distrib]
  ring

theorem expandingLinearized_energy_le (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ M)
    (f : FourierL2) :
    let B := expandingLinearizedPotential a N L ha ha1 hN hL m q
    let D := expandingOrderedPhysicalEnergy a L N hL
    inner ℝ f (B f) ≤
      inner ℝ (expandingLowEnergy a N L hL f) (expandingLowEnergy a N L hL (B f)) +
        ((2 * (m : ℝ) + 1) * M) * ‖expandingHighEnergy a N L hL f‖ ^ 2 +
        ∑ j, inner ℝ (D j f) (expandingOrderedCommutator a L N ha ha1 hN hL m q M hM hQB j f) := by
  intro B D
  have he := expandingLinearized_energy_split a L N ha ha1 hN hL m q M hM hQB f
  have hb := expandingOrderedPrincipal_energy_le a L N m hL
    (expandingUnitTorusFunction a N L q) (expandingUnitTorusFunction a N L q).continuous M hM hQB f
  dsimp only at he hb
  linarith

end DefocusingNLS

end OAI
