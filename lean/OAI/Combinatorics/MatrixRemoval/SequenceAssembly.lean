import OAI.Combinatorics.MatrixRemoval.Model

namespace OAI

/-!
Assembly of the counterexample sequence from two integer bounds.
The existence of a host satisfying both bounds is an explicit hypothesis.
-/

noncomputable section

namespace Problem348.SequenceAssembly

/-- Integer certificates for one candidate host. This does not assert existence. -/
def HostBounds {n : ℕ} (A : BinaryMatrix n) (m : ℕ) : Prop :=
  (∀ B : BinaryMatrix n, HFree fixedH B → m ^ 2 ≤ hammingDistance A B) ∧
    copyCount fixedH A ≤ m * n ^ 130

/-- The sentinel value in `fixedMinEdits` respects every lower bound at most n². -/
theorem fixedMinEdits_ge_of_repairs {n q : ℕ} (A : BinaryMatrix n)
    (hq : q ≤ n * n)
    (hrep : ∀ B : BinaryMatrix n, HFree fixedH B → q ≤ hammingDistance A B) :
    q ≤ fixedMinEdits A := by
  classical
  unfold fixedMinEdits
  apply Finset.le_min'
  intro k hk
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hk
  split_ifs with hB
  · exact hrep B hB
  · omega

/-- Normalize an arbitrary-repair certificate at order n=d*m. -/
theorem fixedDistance_ge_of_integer_bound {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (hrep : ∀ B : BinaryMatrix (d * m), HFree fixedH B →
      m ^ 2 ≤ hammingDistance A B) :
    1 / ((d : ℝ) ^ 2) ≤ fixedDistance A := by
  have hmn : m ≤ d * m := by nlinarith
  have hq : m ^ 2 ≤ (d * m) * (d * m) := by nlinarith
  have hmin := fixedMinEdits_ge_of_repairs A hq hrep
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hminR : (m : ℝ) ^ 2 ≤ (fixedMinEdits A : ℝ) := by exact_mod_cast hmin
  unfold fixedDistance
  push_cast
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) * m) ^ 2)).2
  calc
    1 / ((d : ℝ) ^ 2) * ((d : ℝ) * m) ^ 2 = (m : ℝ) ^ 2 := by
      field_simp
    _ ≤ (fixedMinEdits A : ℝ) := hminR

/-- Normalize the localized-copy integer estimate at order n=d*m. -/
theorem copyDensity_le_of_integer_bound {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (hcount : copyCount fixedH A ≤ m * (d * m) ^ 130) :
    (copyCount fixedH A : ℝ) / (((d * m : ℕ) : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcountR : (copyCount fixedH A : ℝ) ≤
      (m : ℝ) * ((d : ℝ) * m) ^ 130 := by exact_mod_cast hcount
  push_cast
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) * m) ^ 132)).2
  calc
    (copyCount fixedH A : ℝ) ≤ (m : ℝ) * ((d : ℝ) * m) ^ 130 := hcountR
    _ = (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) * ((d : ℝ) * m) ^ 132 := by
      field_simp

/-- The counterexample sequence follows from the integer bounds. -/
theorem counterexample_sequence_of_integer_bounds
    (hcert : ∀ h : ℕ, 1 ≤ h →
      let d : ℕ := 386 * h + 2
      let n : ℕ := d * 2 ^ h
      ∃ A : BinaryMatrix n, HostBounds A (2 ^ h)) :
    ∀ h : ℕ, 1 ≤ h →
      let d : ℕ := 386 * h + 2
      let n : ℕ := d * 2 ^ h
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ 1 / ((d : ℝ) ^ 2) ∧
        (copyCount fixedH A : ℝ) / ((n : ℝ) ^ 132) ≤
          (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  intro h hh
  obtain ⟨A, hrep, hcount⟩ := hcert h hh
  refine ⟨A, fixedDistance_ge_of_integer_bound (by omega)
    (pow_pos (by decide) _) A hrep, ?_⟩
  simpa using copyDensity_le_of_integer_bound (by omega)
    (pow_pos (by decide) _) A hcount

end Problem348.SequenceAssembly

end

end OAI
