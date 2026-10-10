import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusPrincipalPotential

namespace OAI

/-! # Physical ordered components and their principal potential energy

The sum of the squared physical component norms is exactly the high term
of Y_L.  The leading odd-power action has one bound for every derivative
order, using only the profile's pointwise size.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance torusOrderedEnergyMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusOrderedEnergyProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def expandingOrderedPhysicalEnergy (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) : FourierL2 →L[ℂ] Lp ℂ 2 (volume : Measure T) :=
  torusFourierIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (expandingOrderedFourierEnergy a L N hL j)

theorem expandingOrderedPhysicalEnergy_norm (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (f : FourierL2) :
    ‖expandingOrderedPhysicalEnergy a L N hL j f‖ =
      ‖expandingOrderedFourierEnergy a L N hL j f‖ :=
  torusFourierIsometry.norm_map _

theorem expandingOrderedPhysicalEnergy_norm_sq (a L : ℝ) (N : ℕ) (hL : 1 ≤ L) (f : FourierL2) :
    (∑ j : Fin N → Fin 12, ‖expandingOrderedPhysicalEnergy a L N hL j f‖ ^ 2) =
      ‖expandingHighEnergy a N L hL f‖ ^ 2 := by
  simp only [expandingOrderedPhysicalEnergy_norm]
  exact expandingOrderedFourierEnergy_norm_sq a L N hL f

theorem expandingOrderedPhysicalEnergy_inner (a L : ℝ) (N : ℕ) (hL : 1 ≤ L) (f g : FourierL2) :
    (∑ j : Fin N → Fin 12, inner ℝ (expandingOrderedPhysicalEnergy a L N hL j f)
      (expandingOrderedPhysicalEnergy a L N hL j g)) =
      inner ℝ (expandingHighEnergy a N L hL f) (expandingHighEnergy a N L hL g) := by
  have h := expandingOrderedPhysicalEnergy_norm_sq a L N hL (f + g)
  simp only [map_add, norm_add_sq_real, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [expandingOrderedPhysicalEnergy_norm_sq a L N hL f,
    expandingOrderedPhysicalEnergy_norm_sq a L N hL g] at h
  linarith

theorem expandingOrderedPrincipal_energy_le (a L : ℝ) (N m : ℕ) (hL : 1 ≤ L)
    (Q : T → ℂ) (hQ : Continuous Q) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M) (f : FourierL2) :
    (∑ j : Fin N → Fin 12,
      inner ℝ (expandingOrderedPhysicalEnergy a L N hL j f)
        (torusPrincipalPotential m Q hQ M hM hQB (expandingOrderedPhysicalEnergy a L N hL j f))) ≤
      ((2 * (m : ℝ) + 1) * M) * ‖expandingHighEnergy a N L hL f‖ ^ 2 := by
  have h := torusPrincipalPotential_ordered_energy_le m N Q hQ M hM hQB
    (fun j => expandingOrderedPhysicalEnergy a L N hL j f)
  rw [expandingOrderedPhysicalEnergy_norm_sq] at h
  exact h

end DefocusingNLS

end OAI
