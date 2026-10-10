import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.AutomaticCalibrationCorrectness

namespace OAI

/-! The very same rational scale used by the search gives the rational
near-unit lengths supplied to the contact-coordinate program. -/

noncomputable section
namespace ContinuumCoulomb.AutomaticCalibration
open ExactQuantumFactoring.BitStackProgram

def spacing (c : ℚ) (k N : ℕ) : ℚ := RationalLogScale.value c k N

def normalizedValue (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : ℚ :=
  value rho ε c k A B x / spacing c k x.1

theorem spacing_positive {c : ℚ} (hc : 0 < c) (k N : ℕ) (hN : 0 < N) :
    0 < spacing c k N := by
  have hb : 0 < (N ^ k).bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (pow_pos hN k)
  exact mul_pos hc (by exact_mod_cast hb)

theorem normalizedValue_mem (rho : ℕ) {ε c : ℚ} (hε : 0 ≤ ε) (hc : 0 < c)
    (k A B : ℕ) (x : Input) (hN : 0 < x.1) :
    normalizedValue rho ε c k A B x ∈ Set.Icc (1 - ε / 2) (1 + ε / 2) := by
  have hq := spacing_positive hc k x.1 hN
  have hm := value_mem (rho := rho) (k := k) (A := A) (B := B) x hε hc.le
  change (1 - ε / 2) ≤ value rho ε c k A B x / spacing c k x.1 ∧
    value rho ε c k A B x / spacing c k x.1 ≤ (1 + ε / 2)
  constructor
  · apply (le_div_iff₀ hq).mpr
    exact hm.1
  · apply (div_le_iff₀ hq).mpr
    exact hm.2

noncomputable opaque spacingProgram (c : ℚ) (k : ℕ) : Procedure inputCode ratCode
    (fun x => spacing c k x.1) := (RationalLogScale.program c k).comp baseProgram

noncomputable opaque normalizedProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode ratCode (normalizedValue rho ε c k A B) :=
  (Procedure.ratMul.comp ((program rho ε c k A B).pair
    (Procedure.ratInv.comp (spacingProgram c k)))).congrFun
      (by intro x; simp only [Function.comp_apply, normalizedValue, div_eq_mul_inv])

noncomputable def normalizedCertificate (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode ratCode (normalizedValue rho ε c k A B) :=
  (normalizedProgram rho ε c k A B).toTM2

end ContinuumCoulomb.AutomaticCalibration

end

end OAI
