import OAI.NumberTheory.Ostmann.Construction.PrimeShellIndex
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Exact real cells for the selected harmonic word laws -/

namespace Ostmann
open scoped Classical

theorem primeLogIndex_eq_iff (p h : ℕ) (hp : p.Prime) :
    primeLogIndex p = h ↔ (h : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (h : ℝ) + 1 := by
  constructor
  · intro heq
    simpa only [heq] using primeLogIndex_bounds p hp
  · intro hh
    have hi := primeLogIndex_bounds p hp
    by_contra heq
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · have hb : (primeLogIndex p : ℝ) + 1 ≤ h := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith
    · have hb : (h : ℝ) + 1 ≤ primeLogIndex p := by
        exact_mod_cast Nat.succ_le_of_lt hgt
      linarith

/-- Intersecting a whole shell with an integer cell clips its endpoints;
no boundary prime is removed or added. Prescribed exclusions remain intact. -/
theorem primeLogIndex_filter_shell (a b : ℝ) (D : Finset ℕ) (h : ℕ) :
    ((primeLogCellSet 1 0 a b \ D).filter (fun p => primeLogIndex p = h)) =
      primeLogCellSet 1 0 (max a (h : ℝ)) (min b ((h : ℝ) + 1)) \ D := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, mem_primeLogCellSet_iff,
    Nat.modEq_one, true_and, Set.mem_Ioc, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨hp, hlo, hhi⟩, hD⟩, hi⟩
    have hh := (primeLogIndex_eq_iff p h hp).mp hi
    exact ⟨⟨hp, ⟨hlo, hh.1⟩, hhi, hh.2⟩, hD⟩
  · rintro ⟨⟨hp, ⟨hlo, hhl⟩, hhi, hhh⟩, hD⟩
    exact ⟨⟨⟨hp, hlo, hhi⟩, hD⟩, (primeLogIndex_eq_iff p h hp).mpr ⟨hhl, hhh⟩⟩

/-- Passing a selected cell to the common prime sample space preserves its
original harmonic normalizer exactly. -/
theorem primeCellWordPrior_lift (P Q : Finset ℕ) (hQP : Q ⊆ P) (h : ℕ) (p : Q) :
    primeSubsetPrior P (Q.filter (fun q => primeLogIndex q = h)) ⟨p, hQP p.property⟩ =
      primeCellWordPrior Q h p := by
  simp only [primeSubsetPrior, Finset.mem_filter, p.property, true_and,
    primeCellWordPrior, finiteCellMass]

end Ostmann

end OAI
