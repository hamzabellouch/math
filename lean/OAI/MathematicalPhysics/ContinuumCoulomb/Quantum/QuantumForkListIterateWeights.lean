import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNextWeights

namespace OAI

/-! Iterating a fixed number of literal fork rounds preserves a polynomial
coefficient bound. Size uses one uniform envelope for all intermediate lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

def coefficientEnvelope (M L T : ℝ) : ℕ → ℝ
  | 0 => L
  | k+1 => forkCoefficient M (coefficientEnvelope M L T k) T

theorem forkCoefficient_one_le {M L T : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L) :
    1 ≤ forkCoefficient M L T := by
  have h : 0 ≤ (10*M+2)*(forkRadius M L T)^2 := by positivity
  unfold forkCoefficient
  linarith

theorem coefficientEnvelope_one_le {M L T : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L) (k : ℕ) :
    1 ≤ coefficientEnvelope M L T k := by
  induction k with
  | zero => exact hL
  | succ k ih => exact forkCoefficient_one_le hM ih

theorem iterate_mass_le (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.1.length+portMass (iterate N k s).2.2.2 ≤
      s.2.1.length+(4*k+1)*portMass s.2.2.2 := by
  have hb := iterate_bonds_le N s k
  have hp := iterate_portMass_le N s k
  calc
    _ ≤ s.2.1.length+4*k*portMass s.2.2.2+portMass s.2.2.2 := Nat.add_le_add hb hp
    _ = _ := by ring

theorem iterate_coefficientBound (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1)
    (N : ℚ) (hN : 0 ≤ N) {M L T : ℝ} (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : CoefficientBound s L) (k : ℕ)
    (hm : ((s.2.1.length+(4*k+1)*portMass s.2.2.2:ℕ):ℝ) ≤ M) :
    CoefficientBound (iterate N k s) (coefficientEnvelope M L T k) := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    have hkle : s.2.1.length+(4*k+1)*portMass s.2.2.2 ≤
        s.2.1.length+(4*(k+1)+1)*portMass s.2.2.2 := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have hcast : ((s.2.1.length+(4*k+1)*portMass s.2.2.2:ℕ):ℝ) ≤
        ((s.2.1.length+(4*(k+1)+1)*portMass s.2.2.2:ℕ):ℝ) := by exact_mod_cast hkle
    have hm' := hcast.trans hm
    have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hm'
    have hp := iterate_background_valid s hs hb hn N k
    have hmass : (((iterate N k s).2.1.length+
        portMass (iterate N k s).2.2.2:ℕ):ℝ) ≤
        ((s.2.1.length+(4*k+1)*portMass s.2.2.2:ℕ):ℝ) := by
      exact_mod_cast iterate_mass_le N s k
    exact next_coefficientBound (iterate N k s) (iterate_validPorts N s hs k) N
      hp.1 hp.2 hN (hmass.trans hm')
      (coefficientEnvelope_one_le hM0 hL k) hT (ih hm')

end ContinuumCoulomb.QuantumForkList

end

end OAI
