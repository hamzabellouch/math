import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolycyclicDualityComparison

namespace OAI

/-! # Finite integral cohomological dimension excludes torsion

Restriction gives a dimension bound on every cyclic subgroup. Its periodic
integral cohomology contradicts that bound if the subgroup is nontrivial finite.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

variable {G : Type} [Group G]

theorem HasFiniteIntegralCohomologicalDimension.torsionFree
    (hG : HasFiniteIntegralCohomologicalDimension G) : HasNoNontrivialTorsion G := by
  classical
  intro g n hn hgn
  by_contra hg
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hgn⟩
  let H := Subgroup.zpowers g
  let : Fintype H := Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hfin)
  let : CommGroup H := IsCyclic.commGroup
  let : Nontrivial H := ⟨⟨⟨g, Subgroup.mem_zpowers g⟩, 1, fun h => hg (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := H)
  obtain ⟨d, hd⟩ := hG.subgroup H
  let := hd
  let : NeZero (2 * (d + 1)) := ⟨by omega⟩
  exact finiteCyclic_even_cohomology_not_isZero z hz Fintype.one_lt_card
    (2 * (d + 1)) (even_two_mul _) <|
      groupCohomology_isZero_above_dimension d (trivialIntegral H) _ (by omega)

theorem IsIntegralPoincareDualityGroup.torsionFree {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) : HasNoNontrivialTorsion G :=
  (hG.finiteCohomologicalDimension G).torsionFree

end PolycyclicRecognition

end

end OAI
