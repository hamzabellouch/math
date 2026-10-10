import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedScheduleLedger
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordWidthBounds

namespace OAI

/-! # Favorable source ledgers complete the concrete residue schedule -/

namespace LowSpaceSubsetSum.BudgetedSchedule

variable {n g : ℕ}

theorem allowance_le_watchdog (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (hn : 10000 ≤ n) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g)))
    (hcore : (D.coreUnits B families : ℝ) ≤
      (inputScale D.input : ℝ) ^ 410 * (2 : ℝ) ^ ((n + 1) / 2)) :
    allowance D F hF B families ≤ trialWatchdog D.input := by
  have hc : D.coreUnits B families ≤ inputScale D.input ^ 410 * 2 ^ ((n + 1) / 2) := by
    exact_mod_cast hcore
  have hu : 1 ≤ inputScale D.input := by unfold inputScale; omega
  have hp : inputScale D.input ^ (14 + 410) ≤ inputScale D.input ^ 500 :=
    pow_le_pow_right' hu (by omega : 14 + 410 ≤ 500)
  calc
    _ ≤ inputScale D.input ^ 14 * D.coreUnits B families :=
      BudgetedScheduleLedger.allowance_scale D F hF hn B families
    _ ≤ inputScale D.input ^ 14 * (inputScale D.input ^ 410 * 2 ^ ((n + 1) / 2)) :=
      Nat.mul_le_mul_left _ hc
    _ = inputScale D.input ^ (14 + 410) * 2 ^ ((n + 1) / 2) := by
      exact (mul_assoc _ _ _).symm.trans (congrArg (· * 2 ^ ((n + 1) / 2)) (pow_add _ _ _).symm)
    _ ≤ inputScale D.input ^ 500 * 2 ^ ((n + 1) / 2) :=
      Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hp

/-- The watchdog runs the actual prepared-array checker and parent emitter;
the successful semantic event is used only to prove its output. -/
theorem accepts_of_core (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (hcore : (D.coreUnits B (fun i => (families i).map SeparatorStoredMasks.decode) : ℝ) ≤
      (inputScale D.input : ℝ) ^ 410 * (2 : ℝ) ^ ((n + 1) / 2))
    (hyes : D.run B (fun i => (families i).map SeparatorStoredMasks.decode) = true) :
    ∃ left, (run D F hF B (PreparedSeparatorContext.prepare rows families hsize).1
      D.target (trialWatchdog D.input)).1 = some (true, left) := by
  obtain ⟨v, left, he⟩ := complete D F hF B hn hg rows hrows families hsize
    D.target rfl (trialWatchdog D.input) (allowance_le_watchdog D F hF hn B _ hcore)
  have hv := value D F hF B rows hrows families hsize D.target rfl _ v left he
  rw [hyes] at hv
  exact ⟨left, by simpa only [hv] using he⟩

end LowSpaceSubsetSum.BudgetedSchedule

end OAI
