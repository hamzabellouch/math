import OAI.NumberTheory.TwoPoint.Walks.CanonicalPartialWindows

namespace OAI

/-! Enlarging a closed-low logarithmic bin by one bin on its left gives
the strict-low convention in the rough-shift theorem. -/

namespace TwoPointCorrelations

noncomputable def enlargedBinStart (η : ℝ) (j : ℤ) (u : ℕ) : ℝ :=
  Real.exp (((j : ℝ) - 1) * η) / (u : ℝ)

lemma enlargedBinStart_pos (η : ℝ) (j : ℤ) (u : ℕ) (hu : 0 < u) :
    0 < enlargedBinStart η j u :=
  div_pos (Real.exp_pos _) (by exact_mod_cast hu)

lemma enlarged_partial_bin_window (q t z : ℕ) (hq : 0 < q) (ht : 0 < t) (hz : 0 < z)
    (η : ℝ) (hη : 0 < η) (j : ℤ)
    (hbin : actualPaddingBin η (Real.log (t * z : ℕ)) j q) :
    enlargedBinStart η j (q * t) < (z : ℝ) ∧
      (z : ℝ) ≤ Real.exp (2 * η) * enlargedBinStart η j (q * t) := by
  have hw := partial_bin_window q t z hq ht hz η j hbin
  have hup : (0 : ℝ) < (q * t : ℕ) := by exact_mod_cast Nat.mul_pos hq ht
  have hl : enlargedBinStart η j (q * t) <
      Real.exp ((j : ℝ) * η) / (q * t : ℕ) := by
    apply div_lt_div_of_pos_right _ hup
    exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨hl.trans_le hw.1, hw.2.trans_eq ?_⟩
  unfold enlargedBinStart
  rw [← mul_div_assoc, ← mul_div_assoc]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma enlargedBinStart_upper (η : ℝ) (hη : 0 ≤ η) (j : ℤ) (u : ℕ) (hu : 0 < u)
    (U : ℝ) (hU : Real.exp ((j : ℝ) * η) ≤ U) : enlargedBinStart η j u ≤ U := by
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  calc
    _ ≤ Real.exp (((j : ℝ) - 1) * η) :=
      div_le_self (Real.exp_pos _).le hu1
    _ ≤ Real.exp ((j : ℝ) * η) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ U := hU

lemma rough_bin_forces_start_lower {H M τ z : ℝ} (hτ : 0 < τ)
    (hz : H ≤ z) (hupper : z ≤ τ * M) : H / τ ≤ M := by
  apply (div_le_iff₀ hτ).mpr
  nlinarith

end TwoPointCorrelations

end OAI
