import Mathlib.Order.Interval.Set.Union
import OAI.NumberTheory.Ostmann.Construction.PrimeCellPartitionConstruction

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

noncomputable def gridLower {N q : ℕ} (s h : ℝ) (c : Fin N × (ZMod q)ˣ) : ℝ :=
  s + (c.1 : ℝ) * h

noncomputable def gridUpper {N q : ℕ} (s h : ℝ) (c : Fin N × (ZMod q)ˣ) : ℝ :=
  s + ((c.1 : ℝ) + 1) * h

noncomputable def gridResidue {N q : ℕ} (c : Fin N × (ZMod q)ˣ) : ℕ :=
  (c.2 : ZMod q).val

theorem grid_separated {N q : ℕ} [NeZero q] (s h : ℝ) (hh : 0 ≤ h)
    (c d : Fin N × (ZMod q)ˣ) (hcd : c ≠ d) :
    ¬Nat.ModEq q (gridResidue c) (gridResidue d) ∨
      gridUpper s h c ≤ gridLower s h d ∨ gridUpper s h d ≤ gridLower s h c := by
  by_cases hu : c.2 = d.2
  · have hi : c.1 ≠ d.1 := fun hi => hcd (Prod.ext hi hu)
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · right; left
      have hb : (c.1 : ℝ) + 1 ≤ d.1 := by
        exact_mod_cast (show c.1.val + 1 ≤ d.1.val from hlt)
      dsimp [gridUpper, gridLower]
      nlinarith
    · right; right
      have hb : (d.1 : ℝ) + 1 ≤ c.1 := by
        exact_mod_cast (show d.1.val + 1 ≤ c.1.val from hgt)
      dsimp [gridUpper, gridLower]
      nlinarith
  · left
    intro hr
    have heq := (ZMod.natCast_eq_natCast_iff (gridResidue c) (gridResidue d) q).mpr hr
    simp only [gridResidue, ZMod.natCast_zmod_val] at heq
    exact hu (Units.ext heq)

/-- The finite cells used for idealization are constructed directly from
an equal-mesh logarithmic grid and every invertible residue class. -/
noncomputable def gridPrimeCellPartition (N q : ℕ) [NeZero q]
    (hN : 0 < N) (s h : ℝ) (hs : 1 ≤ s) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    PrimeCellPartition
      (primeCellSupport q (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h))
      (Fin N × (ZMod q)ˣ) :=
  buildPrimeCellPartition q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h) (⟨0, hN⟩, 1)
    (fun c => by
      dsimp [gridLower]
      have hp : 0 ≤ (c.1 : ℝ) * h := mul_nonneg (by positivity) hh
      linarith)
    (fun c => by dsimp [gridLower, gridUpper]; nlinarith)
    (fun c => by dsimp [gridLower, gridUpper]; nlinarith)
    (fun c => ZMod.val_coe_unit_coprime c.2)
    (grid_separated s h hh)

theorem mem_primeLogCellSet_iff {q a p : ℕ} {s t : ℝ} :
    p ∈ primeLogCellSet q a s t ↔
      p.Prime ∧ Nat.ModEq q p a ∧ Real.log (p : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hp
    obtain ⟨hI, hprime, hres⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hprime, hres, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hp0).mp hhi)

end Ostmann

end OAI
