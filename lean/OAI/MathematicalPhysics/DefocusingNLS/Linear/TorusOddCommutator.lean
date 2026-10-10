import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusCircularPotential
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOddCommutatorBound

namespace OAI

/-! # The full physical odd-power commutator has uniform high-frequency gain -/

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)

attribute [local irreducible] expandingCircularCoefficient expandingAnticircularCoefficient
  expandingProduct expandingFourierCoefficient expandingOrderedFourierEnergy
  torusPrincipalPotential torusL2Product

theorem torusOddCommutator_identification (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (m : ℕ) (q : FourierL2) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : T, ‖expandingUnitTorusFunction a N L q x‖ ^ (2 * m) ≤ M)
    (f : FourierL2) (j : Fin N → Fin 12) :
    torusFourierIsometry (expandingOddFourierCommutator a L N ha ha1 hN hL m q f j) =
      expandingOrderedCommutator a L N ha ha1 hN hL m q M hM hQB j f := by
  unfold expandingOddFourierCommutator
  rw [map_sub, map_smul, map_add,
    torusFourierIsometry_expanding_convolution a N L ha ha1 hN hL,
    torusFourierIsometry_expanding_convolution a N L ha ha1 hN hL,
    torusFourierIsometry_conjugate]
  have hP := torusPrincipalPotential_circular a N L ha ha1 hN hL m q M hM hQB
    (expandingOrderedPhysicalEnergy a L N hL j f)
  dsimp only [expandingOrderedPhysicalEnergy, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe] at hP
  change torusFourierIsometry (expandingOrderedFourierEnergy a L N hL j
    (expandingLinearizedPotential a N L ha ha1 hN hL m q f)) - _ = _
  rw [← hP]
  rfl

theorem exists_torusOddCommutator_high_bound (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (K : SchwartzMap (EuclideanSpace ℝ (Fin 12)) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L R : ℝ) (hL : 1 ≤ L), 1 ≤ R →
      let q := schwartzTorusSample a (N + 1 : ℕ) L ha1 hN hL K
      ∀ (M : ℝ) (hM : 0 ≤ M)
        (hQB : ∀ x : T, ‖expandingUnitTorusFunction a (N + 1 : ℕ) L q x‖ ^ (2 * m) ≤ M)
        (f : FourierL2) (j : Fin (N + 1) → Fin 12),
      (∀ n : frequencyLattice, ‖n‖ < R * L → f n = 0) →
      ‖expandingOrderedCommutator a L (N + 1) ha ha1 hN hL m q M hM hQB j f‖ ≤ (C / R) * ‖f‖ := by
  obtain ⟨C, hC, hc⟩ := exists_expandingOddFourierCommutator_high_bound a N ha ha1 hN m K
  refine ⟨C, hC, ?_⟩
  intro L R hL hR q M hM hQB f j hf
  rw [← torusOddCommutator_identification a L (N + 1) ha ha1 hN hL m q M hM hQB f j,
    LinearIsometryEquiv.norm_map]
  exact hc L R hL hR f j hf

end DefocusingNLS

end OAI
