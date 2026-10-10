import OAI.NumberTheory.Ostmann.Construction.PrimeCellIdealization

namespace OAI

/-! # Constructing the actual prime log/residue partition

The fiber identities used by the joint comparison follow from separated
log intervals and residue classes. They are not additional distribution
hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeLogCellSet (q a : ℕ) (s t : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter
    (fun p => p.Prime ∧ Nat.ModEq q p a)

theorem primeLogCellSet_disjoint (q a b : ℕ) (s t u v : ℝ)
    (hsep : ¬Nat.ModEq q a b ∨ t ≤ u ∨ v ≤ s) :
    Disjoint (primeLogCellSet q a s t) (primeLogCellSet q b u v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨hpI, hpP, hpA⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpJ, _, hpB⟩ := Finset.mem_filter.mp hp'
  have hi := log_mem_of_mem_exp_interval hpI
  have hj := log_mem_of_mem_exp_interval hpJ
  rcases hsep with hres | htu | hvs
  · exact hres (hpA.symm.trans hpB)
  · linarith [hi.2, hj.1]
  · linarith [hj.2, hi.1]

noncomputable def primeCellSupport {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun c => primeLogCellSet q (a c) (s c) (t c)

noncomputable def primeCellLabel {C : Type*}
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C) (p : ℕ) : C :=
  if h : ∃ c, p ∈ primeLogCellSet q (a c) (s c) (t c) then h.choose else c₀

theorem primeCellLabel_mem {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C) (p : ℕ)
    (hp : p ∈ primeCellSupport q a s t) :
    p ∈ primeLogCellSet q (a (primeCellLabel q a s t c₀ p))
      (s (primeCellLabel q a s t c₀ p)) (t (primeCellLabel q a s t c₀ p)) := by
  have hex : ∃ c, p ∈ primeLogCellSet q (a c) (s c) (t c) := by
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    exact ⟨c, hc⟩
  unfold primeCellLabel
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem primeCellLabel_fiber {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (s t : C → ℝ) (c₀ : C)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ t c ≤ s d ∨ t d ≤ s c)
    (c : C) :
    (primeCellSupport q a s t).filter (fun p => primeCellLabel q a s t c₀ p = c) =
      primeLogCellSet q (a c) (s c) (t c) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hps, hlabel⟩ := Finset.mem_filter.mp hp
    simpa only [hlabel] using primeCellLabel_mem q a s t c₀ p hps
  · intro hp
    have hps : p ∈ primeCellSupport q a s t :=
      Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hp⟩
    refine Finset.mem_filter.mpr ⟨hps, ?_⟩
    by_contra hne
    have hdisj := primeLogCellSet_disjoint q
      (a (primeCellLabel q a s t c₀ p)) (a c)
      (s (primeCellLabel q a s t c₀ p)) (t (primeCellLabel q a s t c₀ p)) (s c) (t c)
      (hsep _ _ hne)
    exact Finset.disjoint_left.mp hdisj (primeCellLabel_mem q a s t c₀ p hps) hp

/-- A fully constructed partition of the actual primes in the selected
log cells. Separation is a numerical/residue property, not an assertion
about the distribution of primes. -/
noncomputable def buildPrimeCellPartition {C : Type*} [Fintype C]
    (q : ℕ) (hq : 1 ≤ q) (a : C → ℕ) (s t : C → ℝ) (c₀ : C)
    (hs : ∀ c, 1 ≤ s c) (hst : ∀ c, s c ≤ t c) (hshort : ∀ c, t c ≤ s c + 1)
    (ha : ∀ c, (a c).Coprime q)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ t c ≤ s d ∨ t d ≤ s c) :
    PrimeCellPartition (primeCellSupport q a s t) C where
  modulus := q
  modulus_pos := hq
  cell := primeCellLabel q a s t c₀
  residue := a
  lower := s
  upper := t
  lower_one := hs
  ordered := hst
  short := hshort
  coprime := ha
  fiber := primeCellLabel_fiber q a s t c₀ hsep

end Ostmann

end OAI
