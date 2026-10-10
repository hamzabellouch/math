import OAI.GroupTheory.PolycyclicRecognition.Algebra.Abelian
import Mathlib.GroupTheory.Solvable

namespace OAI

/-!
# Solvable groups with finitely generated subgroups

Induction on the derived series proves that a solvable group whose subgroups
are all finitely generated has a finite cyclic subnormal series. This is the
algebraic step used for finitely generated nilpotent groups.
-/

namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Restricting to a subgroup preserves finite generation of all subgroups. -/
theorem subgroups_fg_of_subgroups_fg (hfg : ∀ J : Subgroup G, Group.FG J)
    (H : Subgroup G) : ∀ J : Subgroup H, Group.FG J := by
  intro J
  let e := J.equivMapOfInjective H.subtype Subtype.val_injective
  let := hfg (J.map H.subtype)
  exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The derived series of the commutator subgroup maps to the shifted
derived series of the ambient group. -/
theorem map_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator G) n).map (commutator G).subtype =
      derivedSeries G (n + 1) := by
  induction n with
  | zero =>
    change (⊤ : Subgroup (commutator G)).map (commutator G).subtype = commutator G
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, ih]
    rfl

/-- A trivial term in the derived series and finite generation of every
subgroup suffice to construct a finite cyclic series. -/
theorem isPolycyclic_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (G : Type*) [Group G], derivedSeries G n = ⊥ →
      (∀ J : Subgroup G, Group.FG J) → IsPolycyclic G := by
  induction n with
  | zero =>
    intro G _ hn _
    have hsub : Subsingleton G := by
      constructor
      intro x y
      have hx : x = 1 := by
        have h : x ∈ derivedSeries G 0 := Subgroup.mem_top x
        simpa only [hn, Subgroup.mem_bot] using h
      have hy : y = 1 := by
        have h : y ∈ derivedSeries G 0 := Subgroup.mem_top y
        simpa only [hn, Subgroup.mem_bot] using h
      exact hx.trans hy.symm
    exact isPolycyclic_of_subsingleton
  | succ n ih =>
    intro G _ hn hfg
    let N := commutator G
    have hnN : derivedSeries N n = ⊥ := by
      apply Subgroup.map_injective (f := N.subtype) Subtype.val_injective
      rw [Subgroup.map_bot, map_derivedSeries_commutator, hn]
    have hN : IsPolycyclic N := ih N hnN (subgroups_fg_of_subgroups_fg hfg N)
    let : Group.FG G := Group.fg_def.mpr
      ((Group.fg_iff_subgroup_fg (⊤ : Subgroup G)).mp (hfg ⊤))
    have hQ : IsPolycyclic (G ⧸ N) := isPolycyclic_of_finitelyGenerated_commGroup _
    exact isPolycyclic_of_normal_subgroup N hN hQ

/-- A solvable group with all subgroups finitely generated is polycyclic. -/
theorem isPolycyclic_of_solvable_subgroups_fg [Group.IsSolvable G]
    (hfg : ∀ J : Subgroup G, Group.FG J) : IsPolycyclic G := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact isPolycyclic_of_derivedSeries_eq_bot n G hn hfg

end PolycyclicRecognition

end OAI
