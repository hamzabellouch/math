import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualSolvableDimension

namespace OAI

/-! # Passing finite virtual dimension through a polycyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
open ChromaticCyclic
variable {G : Type} [Group G]

theorem exists_solvable_finiteDimension_of_cyclicSeries
    {H K : Subgroup G} {n : ℕ} (c : CyclicSeries H K n) (hfg : Group.FG H)
    (hH : ∃ V : Subgroup H, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V) :
    ∃ V : Subgroup K, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) ∧
      ∃ V : Subgroup (c.group i), V.FiniteIndex ∧ Group.IsSolvable V ∧
        HasFiniteIntegralCohomologicalDimension V := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨hfg, hH⟩
    | succ i ih =>
      intro hi
      obtain ⟨hfg, hprev⟩ := ih (by omega)
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      let : Group.FG ((c.group i).subgroupOf (c.group (i + 1))) :=
        @Group.fg_of_surjective _ _ _ _ hfg e.toMonoidHom e.surjective
      exact ⟨finitelyGenerated_of_cyclicStep s hfg,
        exists_solvable_finiteDimension_of_cyclic_extension
          ((c.group i).subgroupOf (c.group (i + 1)))
          (exists_solvable_finiteDimension_of_equiv e hprev)⟩
  have htop := (hm n le_rfl).2
  rwa [c.last] at htop

theorem exists_solvable_finiteDimension_of_virtuallyPolycyclic_quotient
    (N : Subgroup G) [N.Normal] [Group.FG N]
    (hN : ∃ V : Subgroup N, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V)
    (hQ : IsVirtuallyPolycyclic (G ⧸ N)) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  obtain ⟨P, hPindex, n, ⟨c⟩⟩ := hQ
  let := hPindex
  let q := QuotientGroup.mk' N
  let H := P.comap q
  have cQ := c.map P.subtype
  rw [Subgroup.map_bot, Subgroup.map_top, Subgroup.range_subtype] at cQ
  have cG := cQ.comap q
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk'] at cG
  exact exists_solvable_finiteDimension_of_finiteIndex H
    (exists_solvable_finiteDimension_of_cyclicSeries cG inferInstance hN)

end PolycyclicRecognition

end

end OAI
