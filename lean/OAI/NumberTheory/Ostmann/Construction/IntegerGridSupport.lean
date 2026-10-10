import Mathlib.Order.Interval.Set.Union
import OAI.NumberTheory.Ostmann.Construction.IntegerCellPriors

namespace OAI

/-! # Constructing the external-integer log/residue partition

The fiber identities used by the joint comparison follow from separated
log intervals and residue classes. They are not additional distribution
hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def integerLogCellSet (q a : ℕ) (s t : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter
    (fun p => Nat.ModEq q p a)

theorem integerLogCellSet_disjoint (q a b : ℕ) (s t u v : ℝ)
    (hsep : ¬Nat.ModEq q a b ∨ t ≤ u ∨ v ≤ s) :
    Disjoint (integerLogCellSet q a s t) (integerLogCellSet q b u v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨hpI, hpA⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpJ, hpB⟩ := Finset.mem_filter.mp hp'
  have hi := log_mem_of_mem_exp_interval hpI
  have hj := log_mem_of_mem_exp_interval hpJ
  rcases hsep with hres | htu | hvs
  · exact hres (hpA.symm.trans hpB)
  · linarith [hi.2, hj.1]
  · linarith [hj.2, hi.1]

noncomputable def integerCellSupport {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun c => integerLogCellSet q (a c) (s c) (t c)

noncomputable def integerCellLabel {C : Type*}
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C) (p : ℕ) : C :=
  if h : ∃ c, p ∈ integerLogCellSet q (a c) (s c) (t c) then h.choose else c₀

theorem integerCellLabel_mem {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C) (p : ℕ)
    (hp : p ∈ integerCellSupport q a s t) :
    p ∈ integerLogCellSet q (a (integerCellLabel q a s t c₀ p))
      (s (integerCellLabel q a s t c₀ p)) (t (integerCellLabel q a s t c₀ p)) := by
  have hex : ∃ c, p ∈ integerLogCellSet q (a c) (s c) (t c) := by
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    exact ⟨c, hc⟩
  unfold integerCellLabel
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem integerCellLabel_fiber {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ t c ≤ s d ∨ t d ≤ s c)
    (c : C) :
    (integerCellSupport q a s t).filter (fun p => integerCellLabel q a s t c₀ p = c) =
      integerLogCellSet q (a c) (s c) (t c) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hps, hlabel⟩ := Finset.mem_filter.mp hp
    simpa only [hlabel] using integerCellLabel_mem q a s t c₀ p hps
  · intro hp
    have hps : p ∈ integerCellSupport q a s t :=
      Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hp⟩
    refine Finset.mem_filter.mpr ⟨hps, ?_⟩
    by_contra hne
    have hdisj := integerLogCellSet_disjoint q
      (a (integerCellLabel q a s t c₀ p)) (a c)
      (s (integerCellLabel q a s t c₀ p)) (t (integerCellLabel q a s t c₀ p)) (s c) (t c)
      (hsep _ _ hne)
    exact Finset.disjoint_left.mp hdisj (integerCellLabel_mem q a s t c₀ p hps) hp

/-- A fully constructed partition of the actual integers in the selected
log cells. Separation is a numerical/residue property, not an assertion
about the distribution of integers. -/
noncomputable def buildIntegerCellPartition {C : Type*} [Fintype C]
    (q : ℕ) (hq : 0 < q) (a : C → ℕ) (s t : C → ℝ) (c₀ : C)
    (hst : ∀ c, s c ≤ t c) (hshort : ∀ c, t c ≤ s c + 1)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ t c ≤ s d ∨ t d ≤ s c) :
    IntegerCellPartition (integerCellSupport q a s t) C where
  modulus := q
  modulus_pos := hq
  cell := integerCellLabel q a s t c₀
  residue := a
  lower := s
  upper := t
  ordered := hst
  short := hshort
  fiber := integerCellLabel_fiber q a s t c₀ hsep

noncomputable def integerGridLower {N q : ℕ} (s h : ℝ) (c : Fin N × ZMod q) : ℝ :=
  s + (c.1 : ℝ) * h

noncomputable def integerGridUpper {N q : ℕ} (s h : ℝ) (c : Fin N × ZMod q) : ℝ :=
  s + ((c.1 : ℝ) + 1) * h

theorem integerGrid_separated {N q : ℕ} [NeZero q] (s h : ℝ) (hh : 0 ≤ h)
    (c d : Fin N × ZMod q) (hcd : c ≠ d) :
    ¬Nat.ModEq q c.2.val d.2.val ∨
      integerGridUpper s h c ≤ integerGridLower s h d ∨
      integerGridUpper s h d ≤ integerGridLower s h c := by
  by_cases hu : c.2 = d.2
  · have hi : c.1 ≠ d.1 := fun hi => hcd (Prod.ext hi hu)
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · right; left
      have hb : (c.1 : ℝ) + 1 ≤ d.1 := by
        exact_mod_cast (show c.1.val + 1 ≤ d.1.val from hlt)
      dsimp [integerGridUpper, integerGridLower]
      nlinarith
    · right; right
      have hb : (d.1 : ℝ) + 1 ≤ c.1 := by
        exact_mod_cast (show d.1.val + 1 ≤ c.1.val from hgt)
      dsimp [integerGridUpper, integerGridLower]
      nlinarith
  · left
    intro hr
    have heq := (ZMod.natCast_eq_natCast_iff c.2.val d.2.val q).mpr hr
    simp only [ZMod.natCast_zmod_val] at heq
    exact hu heq

noncomputable def gridIntegerCellPartition (N q : ℕ) [NeZero q]
    (hN : 0 < N) (s h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    IntegerCellPartition
      (integerCellSupport q (fun c : Fin N × ZMod q => c.2.val)
        (integerGridLower s h) (integerGridUpper s h)) (Fin N × ZMod q) :=
  buildIntegerCellPartition (C := Fin N × ZMod q) q (NeZero.pos q)
    (fun c : Fin N × ZMod q => c.2.val)
    (integerGridLower (q := q) s h) (integerGridUpper (q := q) s h) (⟨0, hN⟩, 0)
    (fun c => by dsimp [integerGridLower, integerGridUpper]; nlinarith)
    (fun c => by dsimp [integerGridLower, integerGridUpper]; nlinarith)
    (integerGrid_separated s h hh)

theorem mem_integerLogCellSet_iff {q a n : ℕ} {s t : ℝ} :
    n ∈ integerLogCellSet q a s t ↔
      0 < n ∧ Nat.ModEq q n a ∧ Real.log (n : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hn
    obtain ⟨hI, hres⟩ := Finset.mem_filter.mp hn
    exact ⟨lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hI).1,
      hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hn, hres, hlo, hhi⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hn0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hn0).mp hhi)

/-- All residue classes are used for the external giant. The constructed
support is exactly the original interval of positive integers. -/
theorem mem_gridIntegerSupport_iff (N q : ℕ) [NeZero q] (s h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    n ∈ integerCellSupport q (fun c : Fin N × ZMod q => c.2.val)
      (integerGridLower s h) (integerGridUpper s h) ↔
      0 < n ∧ Real.log (n : ℝ) ∈ Set.Ioc s (s + N * h) := by
  constructor
  · intro hn
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hn0, _, hlo, hhi⟩ := mem_integerLogCellSet_iff.mp hc
    have hj : (c.1 : ℝ) + 1 ≤ N := by
      exact_mod_cast (show c.1.val + 1 ≤ N from c.1.isLt)
    have hj0 : (0 : ℝ) ≤ c.1 := by positivity
    dsimp [integerGridLower, integerGridUpper] at hlo hhi
    exact ⟨hn0, by nlinarith, by nlinarith⟩
  · rintro ⟨hn0, hlog⟩
    have hmem : Real.log (n : ℝ) ∈
        Set.Ioc ((fun j : ℕ => s + j * h) 0) ((fun j : ℕ => s + j * h) N) := by
      simpa using hlog
    have hu := Ioc_subset_biUnion_Ioc N (fun j : ℕ => s + j * h) hmem
    simp only [Set.mem_iUnion] at hu
    obtain ⟨j, hj, hbound⟩ := hu
    let c : Fin N × ZMod q := (⟨j, Finset.mem_range.mp hj⟩, n)
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ c, mem_integerLogCellSet_iff.mpr ⟨hn0, ?_, ?_⟩⟩
    · apply (ZMod.natCast_eq_natCast_iff n c.2.val q).mp
      simp [c]
    · simpa only [c, integerGridLower, integerGridUpper, Nat.cast_add, Nat.cast_one] using hbound

end Ostmann

end OAI
