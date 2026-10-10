import OAI.NumberTheory.Ostmann.Arithmetic.PrimeWordCellGeometry
import OAI.NumberTheory.Ostmann.Construction.UnitPrimeCellSupport
import OAI.NumberTheory.Ostmann.Construction.FrozenPrimeDeletions

namespace OAI

/-! # The exact selected word cells in the bulk prime comparison -/

namespace Ostmann
open scoped Classical BigOperators

/-- The selected integer log cell clipped to its original shell. -/
noncomputable def wordCellSupport (a b : ℝ) (h : ℕ) : Finset ℕ :=
  primeLogCellSet 1 0 (max a (h : ℝ)) (min b ((h : ℝ) + 1))

theorem wordCellSupport_eq_filter (a b : ℝ) (D : Finset ℕ) (h : ℕ) :
    wordCellSupport a b h \ D =
      ((primeLogCellSet 1 0 a b \ D).filter (fun p => primeLogIndex p = h)) :=
  (primeLogIndex_filter_shell a b D h).symm

/-- The cell mass used when selecting the word is precisely the mass used by
its original normalized prime law in the subsequent comparison. -/
theorem wordCellSupport_mass (a b : ℝ) (D : Finset ℕ) (h : ℕ) :
    (∑ p ∈ wordCellSupport a b h \ D, (p : ℝ)⁻¹) =
      finiteCellMass (primeLogCellSet 1 0 a b \ D) primeLogIndex (fun p => (p : ℝ)⁻¹) h := by
  rw [wordCellSupport_eq_filter]
  rfl

theorem wordCellSupport_geometry (a b : ℝ) (D : Finset ℕ) (h : ℕ)
    (hm : 0 < finiteCellMass (primeLogCellSet 1 0 a b \ D)
      primeLogIndex (fun p => (p : ℝ)⁻¹) h) :
    max a (h : ℝ) ≤ min b ((h : ℝ) + 1) ∧
      min b ((h : ℝ) + 1) ≤ max a (h : ℝ) + 1 := by
  have hn : (wordCellSupport a b h \ D).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [← wordCellSupport_mass, he] at hm
    simp only [Finset.sum_empty, lt_self_iff_false] at hm
  obtain ⟨p, hp⟩ := hn
  have hp' := (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1).2.2
  exact ⟨hp'.1.le.trans hp'.2,
    (min_le_right _ _).trans (add_le_add (le_max_right _ _) le_rfl)⟩

theorem wordCellSupport_unit_residues (q : ℕ) [NeZero q] (a b : ℝ) (h : ℕ)
    (hq : (q : ℝ) ≤ Real.exp (max a (h : ℝ))) :
    primeCellSupport q (fun c : Unit × (ZMod q)ˣ => c.2.val.val)
      (fun _ => max a (h : ℝ)) (fun _ => min b ((h : ℝ) + 1)) =
        wordCellSupport a b h := by
  rw [unitPrimeCellSupport_eq q (fun _ : Unit => max a (h : ℝ))
    (fun _ => min b ((h : ℝ) + 1)) (fun _ => hq)]
  simp only [primeCellSupport, Finset.univ_unique, Finset.singleton_biUnion,
    wordCellSupport]

/-- The full cell has at least its mass after the fixed global exclusions. -/
theorem wordCellSupport_mass_lower (a b : ℝ) (D : Finset ℕ) (h : ℕ) (c : ℝ)
    (hm : c ≤ finiteCellMass (primeLogCellSet 1 0 a b \ D)
      primeLogIndex (fun p => (p : ℝ)⁻¹) h) :
    c ≤ ∑ p ∈ wordCellSupport a b h, (p : ℝ)⁻¹ := by
  rw [← wordCellSupport_mass] at hm
  exact hm.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
    (fun _ _ _ => by positivity))

/-- Freezing nonbulk primes only enlarges the set deleted for the comparison;
the law to which the answer is returned still has just its global exclusions. -/
theorem wordCellSupport_frozen_deletions {σ J : Type*} [Fintype σ]
    (a b : ℝ) (h : ℕ) (D : Finset ℕ) (base : σ → ℕ) (slot : J ↪ σ)
    (outside : List ℕ) :
    let deleted := D ∪ frozenPrimeDeletions base slot outside
    (wordCellSupport a b h \ D ⊆ wordCellSupport a b h) ∧
    (wordCellSupport a b h \ deleted ⊆ wordCellSupport a b h \ D) ∧
    deleted.card ≤ D.card + Fintype.card σ + outside.length ∧
    (∀ i, i ∉ Set.range slot → base i ∈ deleted) ∧
    (∀ p ∈ outside, p ∈ deleted) := by
  dsimp only
  refine ⟨Finset.sdiff_subset, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp).1,
      fun hD => (Finset.mem_sdiff.mp hp).2 (Finset.mem_union_left _ hD)⟩
  · exact (Finset.card_union_le D _).trans
      ((Nat.add_le_add_left (frozenPrimeDeletions_card_le base slot outside) D.card).trans_eq
        (Nat.add_assoc _ _ _).symm)
  · intro i hi
    exact Finset.mem_union_right _ (mem_frozenPrimeDeletions_base base slot outside i hi)
  · intro p hp
    exact Finset.mem_union_right _ (mem_frozenPrimeDeletions_outside base slot outside p hp)

end Ostmann

end OAI
