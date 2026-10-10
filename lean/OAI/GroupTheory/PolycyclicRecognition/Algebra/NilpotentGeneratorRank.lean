import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerExtensionRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolyZ

namespace OAI

/-! # Uniform generator bounds for nilpotent subgroups

Along a torsion-free cyclic series the duality dimension counts the infinite
factors, each of which adds at most one generator. Thus an ambient integral
cohomological-dimension bound controls the number of generators of every
finitely generated nilpotent subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

theorem exists_poincareDuality_rank_bound_of_cyclic_quotient
    [Group.FG G] (N : Subgroup G) [N.Normal] [Group.FG N] [IsCyclic (G ⧸ N)]
    (hN : ∃ n, IsIntegralPoincareDualityGroup N n ∧ Group.rank N ≤ n)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) :
    ∃ n, IsIntegralPoincareDualityGroup G n ∧ Group.rank G ≤ n := by
  obtain ⟨n, hn, hr⟩ := hN
  cases finite_or_infinite (G ⧸ N) with
  | inr h =>
    let := h
    exact ⟨n + 1, poincareDuality_of_infiniteCyclicQuotient N hn,
      (rank_le_add_one_of_infiniteCyclicQuotient N).trans (Nat.add_le_add_right hr 1)⟩
  | inl h =>
    let := h
    let := subsingleton_of_finite_torsionFree (G ⧸ N) hQ
    have htop : N = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    subst N
    refine ⟨n, hn.of_equiv Subgroup.topEquiv, ?_⟩
    calc
      Group.rank G = Group.rank (⊤ : Subgroup G) :=
        (Group.rank_congr (Subgroup.topEquiv (G := G))).symm
      _ ≤ n := hr

theorem IsPolyZ.exists_poincareDuality_rank_bound (hG : IsPolyZ G) :
    letI := hG.isPolycyclic.finitelyGenerated
    ∃ n, IsIntegralPoincareDualityGroup G n ∧ Group.rank G ≤ n := by
  let : Group.FG G := hG.isPolycyclic.finitelyGenerated
  have hpoly : IsPolycyclic G := hG.isPolycyclic
  obtain ⟨n, c, hc⟩ := hG
  let (i : ℕ) : Group.FG (c.group i) :=
    (hpoly.of_injective (c.group i).subtype Subtype.val_injective).finitelyGenerated
  have hm : ∀ i, i ≤ n → ∃ d, IsIntegralPoincareDualityGroup (c.group i) d ∧
      Group.rank (c.group i) ≤ d := by
    intro i
    induction i with
    | zero =>
      intro _
      let : Subsingleton (c.group 0) :=
        c.first.symm ▸ (inferInstance : Subsingleton (⊥ : Subgroup G))
      exact ⟨0, poincareDuality_zero_of_subsingleton _, le_of_eq (Group.rank_eq_zero _)⟩
    | succ i ih =>
      intro hi
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let N := (c.group i).subgroupOf (c.group (i + 1))
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      let : Group.FG N := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
      obtain ⟨d, hd, hr⟩ := ih (by omega)
      have hrN : Group.rank N ≤ d := by
        calc
          Group.rank N = Group.rank (c.group i) := (Group.rank_congr e).symm
          _ ≤ d := hr
      exact exists_poincareDuality_rank_bound_of_cyclic_quotient N
        ⟨d, hd.of_equiv e, hrN⟩ (hc i (by omega))
  obtain ⟨d, hd, hr⟩ := hm n le_rfl
  let e := (MulEquiv.subgroupCongr c.last).trans Subgroup.topEquiv
  refine ⟨d, hd.of_equiv e, ?_⟩
  calc
    Group.rank G = Group.rank (c.group n) := (Group.rank_congr e).symm
    _ ≤ d := hr

theorem nilpotent_subgroup_generator_rank_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [Group.FG H] [Group.IsNilpotent H] : Group.rank H ≤ d := by
  let := subgroup_cohomologicalDimension_le H d
  have htf : HasNoNontrivialTorsion H :=
    (show HasFiniteIntegralCohomologicalDimension H from ⟨d, inferInstance⟩).torsionFree
  obtain ⟨n, hn, hr⟩ := (nilpotent_polyZ_of_finitelyGenerated_torsionFree htf).exists_poincareDuality_rank_bound
  exact hr.trans hn.dimension_le

theorem HasFiniteIntegralCohomologicalDimension.bounds_nilpotent_generator_rank
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∀ (H : Subgroup G) [Group.FG H] [Group.IsNilpotent H], Group.rank H ≤ d := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨d, fun H _ _ => nilpotent_subgroup_generator_rank_le d H⟩

end PolycyclicRecognition

end

end OAI
