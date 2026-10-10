import OAI.Combinatorics.ProgressionColoring.CyclicModel

namespace OAI

/-! Geometric consequences of the actual cyclic representative system. -/

namespace QuantitativeVanDerWaerden

/-- The coordinate lattice is unchanged when a real step is shifted by an integer. -/
theorem yRep_step_lattice {q D dilation : ℕ} (hq : 0 < q)
    (d : CyclicGroup q D) (i : Fin D) {w : ℝ}
    (hstep : ∃ z : ℤ, yRep q D dilation d i - w = z) :
    ∃ z : ℤ, (q : ℝ) ^ (i.val + 1) * w = z := by
  obtain ⟨z₁, h₁⟩ := yRep_lattice q D dilation d i hq
  obtain ⟨z₂, h₂⟩ := hstep
  refine ⟨z₁ - (q : ℤ) ^ (i.val + 1) * z₂, ?_⟩
  push_cast
  nlinarith [congrArg (fun t : ℝ => (q : ℝ) ^ (i.val + 1) * t) h₂]

/-- Every nonzero lifted coordinate step is at least one coordinate lattice unit. -/
theorem yRep_step_abs_lower {q D dilation : ℕ} (hq : 0 < q)
    (d : CyclicGroup q D) (i : Fin D) {w : ℝ}
    (hstep : ∃ z : ℤ, yRep q D dilation d i - w = z) (hw : w ≠ 0) :
    1 / (q : ℝ) ^ (i.val + 1) ≤ |w| := by
  have hlat : ∃ z : ℤ, ((q ^ (i.val + 1) : ℕ) : ℝ) * w = z := by
    simpa only [Nat.cast_pow] using yRep_step_lattice hq d i hstep
  simpa only [Nat.cast_pow] using lattice_separation (pow_pos hq (i.val + 1)) hlat hw

/-- The mesh cutoff `q^(-(D+1))` lies below every nonzero lifted step. -/
theorem yRep_step_mesh_lower {q D dilation : ℕ} (hq : 0 < q)
    (d : CyclicGroup q D) (i : Fin D) {w : ℝ}
    (hstep : ∃ z : ℤ, yRep q D dilation d i - w = z) (hw : w ≠ 0) :
    1 / (q : ℝ) ^ (D + 1) ≤ 1 / (q : ℝ) ^ D ∧
      1 / (q : ℝ) ^ D ≤ |w| := by
  have hqN : 1 ≤ q := hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqN
  have hpow : 0 < (q : ℝ) ^ (i.val + 1) := by positivity
  constructor
  · exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ hqR (Nat.le_succ D))
  · exact (one_div_le_one_div_of_le hpow
      (pow_le_pow_right₀ hqR (show i.val + 1 ≤ D from i.isLt))).trans
        (yRep_step_abs_lower hq d i hstep hw)

end QuantitativeVanDerWaerden

end OAI
