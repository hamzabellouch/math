import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.BoundedInnerNull

namespace OAI

/-! # The exact nonprincipal energy error vanishes on locally null sequences -/

open Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)
noncomputable local instance compactEnergyErrorMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance compactEnergyErrorProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (a Q M : ℝ) (N : ℕ) (ha : 0 < a) (ha1 : a < 1)
  (hN : 8 < ((N + 1 : ℕ) : ℝ)) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
  (hLinf : Tendsto L atTop atTop) (q : ℕ → FourierL2)
  (hq : ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hN L hL q) (hqb : ∀ n, ‖q n‖ ≤ Q)
  (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
  (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
    ‖expandingTorusFunction a (N + 1 : ℕ) (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
  (m : ℕ) (hm : 0 < m) (P : ℝ) (hP : 0 ≤ P)
  (hQB : ∀ n (x : T), ‖expandingUnitTorusFunction a (N + 1 : ℕ) (L n) (q n) x‖ ^ (2 * m) ≤ P)

include hLinf hq hqb hf hlocal hm in
theorem tendsto_expandingOrderedCommutator (j : Fin (N + 1) → Fin 12) :
    Tendsto (fun n => expandingOrderedCommutator a (L n) (N + 1) ha ha1 hN (hL n)
      m (q n) P hP (hQB n) j (f n)) atTop (𝓝 0) := by
  have ht := tendsto_expandingOddFourierCommutator a Q M N ha ha1 hN L hL hLinf q hq hqb f hf hlocal m hm j
  have hi := (torusFourierIsometry.continuous.tendsto 0).comp ht
  simp only [Function.comp_def, map_zero] at hi
  have he (n : ℕ) : torusFourierIsometry (expandingOddFourierCommutator a (L n) (N + 1)
      ha ha1 hN (hL n) m (q n) (f n) j) =
      expandingOrderedCommutator a (L n) (N + 1) ha ha1 hN (hL n) m (q n) P hP (hQB n) j (f n) :=
    torusOddCommutator_identification a (L n) (N + 1) ha ha1 hN (hL n) m (q n) P hP (hQB n) (f n) j
  simpa only [he] using hi

include hLinf hq hqb hf hlocal hm in
theorem tendsto_expandingCompactEnergy_error :
    Tendsto (fun n =>
      inner ℝ (f n) (expandingLinearizedPotential a (N + 1 : ℕ) (L n) ha ha1 hN (hL n) m (q n) (f n)) -
        ∑ j : Fin (N + 1) → Fin 12,
          inner ℝ (expandingOrderedPhysicalEnergy a (L n) (N + 1) (hL n) j (f n))
            (torusPrincipalPotential m (expandingUnitTorusFunction a (N + 1 : ℕ) (L n) (q n))
              (expandingUnitTorusFunction a (N + 1 : ℕ) (L n) (q n)).continuous P hP (hQB n)
              (expandingOrderedPhysicalEnergy a (L n) (N + 1) (hL n) j (f n)))) atTop (𝓝 0) := by
  have hlo := tendsto_expandingLinearized_lowEnergy a Q M N ha ha1 hN L hL hLinf q hq hqb f hf hlocal m hm
  have hlow := tendsto_inner_of_bounded_null
    (fun n => expandingLowEnergy a (N + 1 : ℕ) (L n) (hL n) (f n)) _ M
    (fun n => (expandingLowEnergy_norm_le a _ _ _ _).trans (hf n)) hlo
  have htop (j : Fin (N + 1) → Fin 12) := tendsto_inner_of_bounded_null
    (fun n => expandingOrderedPhysicalEnergy a (L n) (N + 1) (hL n) j (f n)) _ M
    (fun n => (expandingOrderedPhysicalEnergy_norm a _ _ _ _ _).le.trans
      ((expandingOrderedFourierEnergy_norm_le a _ _ _ _ _).trans (hf n)))
    (tendsto_expandingOrderedCommutator a Q M N ha ha1 hN L hL hLinf q hq hqb f hf hlocal m hm P hP hQB j)
  have ht := hlow.add (tendsto_finsetSum Finset.univ (fun j _ => htop j))
  simp only [Finset.sum_const_zero, add_zero] at ht
  have he (n : ℕ) := expandingLinearized_energy_split a (L n) (N + 1) ha ha1 hN (hL n)
    m (q n) P hP (hQB n) (f n)
  dsimp only at he
  convert ht using 1
  funext n
  linarith [he n]

end DefocusingNLS

end OAI
