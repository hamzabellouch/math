import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductCommutatorBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LatticeMomentAlgebra

namespace OAI

/-! # Polynomial moments supply the high-frequency commutator estimate -/

namespace DefocusingNLS

theorem latticeMoment_to_commutator (L : ℝ) (hL : 1 ≤ L) (N : ℕ)
    (c : frequencyLattice → ℂ) (hc : Summable (latticeMomentMass L (N + 1) c)) :
    Summable (expandingCommutatorMoment L N c) ∧
      (∑' m, expandingCommutatorMoment L N c m) ≤
        2 ^ N * ∑' m, latticeMomentMass L (N + 1) c m := by
  have hpoint (m : frequencyLattice) : expandingCommutatorMoment L N c m ≤
      2 ^ N * latticeMomentMass L (N + 1) c m := by
    have hLp : 0 < L := by linarith
    have hr : 0 ≤ ‖m‖ / L := div_nonneg (norm_nonneg _) hLp.le
    have hpoly : (‖m‖ / L) * (2 + ‖m‖ / L) ^ N ≤
        2 ^ N * (1 + ‖m‖ / L) ^ (N + 1) := by
      calc
        _ ≤ (1 + ‖m‖ / L) * (2 * (1 + ‖m‖ / L)) ^ N := by gcongr <;> linarith
        _ = _ := by rw [mul_pow, pow_succ]; ring
    have h := mul_le_mul_of_nonneg_left hpoly (norm_nonneg (c m))
    dsimp only [expandingCommutatorMoment, latticeMomentMass, latticeMomentWeight]
    convert h using 1 <;> ring
  have hs := Summable.of_nonneg_of_le (expandingCommutatorMoment_nonneg L hL N c)
    hpoint (hc.mul_left (2 ^ N))
  exact ⟨hs, (hs.tsum_le_tsum hpoint (hc.mul_left _)).trans_eq tsum_mul_left⟩

theorem expandingProductCommutator_high_moment (a L R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (hL : 1 ≤ L) (hR : 1 ≤ R) (j : Fin (N + 1) → Fin 12) (q f : FourierL2)
    (hM : Summable (latticeMomentMass L (N + 1) (expandingFourierCoefficient a (N + 1 : ℕ) L q)))
    (hf : ∀ n : frequencyLattice, ‖n‖ < R * L → f n = 0) :
    ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j q f‖ ≤
      ((N + 1 : ℕ) / R) * (2 ^ N *
        ∑' m, latticeMomentMass L (N + 1) (expandingFourierCoefficient a (N + 1 : ℕ) L q) m) * ‖f‖ := by
  obtain ⟨hs, hb⟩ := latticeMoment_to_commutator L hL N _ hM
  exact (expandingProductCommutator_high_norm_le a L R N ha ha1 hN hL hR j q f hs hf).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (norm_nonneg f))

end DefocusingNLS

end OAI
