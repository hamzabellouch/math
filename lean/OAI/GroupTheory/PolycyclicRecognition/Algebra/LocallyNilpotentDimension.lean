import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentClassBound
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareDualityBase

namespace OAI

/-! # Finite integral dimension makes local nilpotence uniform

Every element of a lower-central term is witnessed in a finitely generated
subgroup. The common class bound from cohomological dimension therefore makes
a locally nilpotent group nilpotent, including groups not finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement

variable {G : Type} [Group G]

def fgLowerCentralSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H : Subgroup G, H.FG ∧ g ∈ H.lowerCentralSeries n}
  one_mem' := ⟨⊥, Subgroup.FG.bot, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    exact ⟨H ⊔ K, hH.sup hK, Subgroup.mul_mem _
      (Subgroup.lowerCentralSeries_mono n le_sup_left hx)
      (Subgroup.lowerCentralSeries_mono n le_sup_right hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

theorem lowerCentralSeries_le_fgLowerCentral (n : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries n ≤ fgLowerCentralSubgroup n := by
  induction n with
  | zero =>
    intro g _
    refine ⟨Subgroup.closure {g}, ?_, Subgroup.subset_closure (Set.mem_singleton g)⟩
    exact (Subgroup.fg_iff _).mpr ⟨{g}, rfl, Set.finite_singleton g⟩
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y _
    obtain ⟨H, hH, hxH⟩ := ih hx
    let K := H ⊔ Subgroup.closure {y}
    have hY : (Subgroup.closure {y}).FG :=
      (Subgroup.fg_iff _).mpr ⟨{y}, rfl, Set.finite_singleton y⟩
    refine ⟨K, hH.sup hY, ?_⟩
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.lowerCentralSeries_mono n le_sup_left hxH)
      ((show Subgroup.closure {y} ≤ K from le_sup_right)
        (Subgroup.subset_closure (Set.mem_singleton y)))

theorem lowerCentralSeries_eq_bot_of_fg_subgroups (n : ℕ)
    (h : ∀ H : Subgroup G, H.FG → H.lowerCentralSeries n = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries n = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := lowerCentralSeries_le_fgLowerCentral n hg
  simpa only [h H hH] using hgH

theorem locallyNilpotent_lowerCentralSeries_bound (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (hlocal : ∀ H : Subgroup G, Group.FG H → Group.IsNilpotent H) :
    (⊤ : Subgroup G).lowerCentralSeries (2 * d) = ⊥ := by
  apply lowerCentralSeries_eq_bot_of_fg_subgroups
  intro H hH
  have hfg : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let := hlocal H hfg
  exact Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le
    (nilpotent_subgroup_class_le d H)

theorem HasFiniteIntegralCohomologicalDimension.nilpotent_of_locallyNilpotent
    (hG : HasFiniteIntegralCohomologicalDimension G)
    (hlocal : ∀ H : Subgroup G, Group.FG H → Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨2 * d, locallyNilpotent_lowerCentralSeries_bound d hlocal⟩

theorem IsIntegralPoincareDualityGroup.polycyclic_of_locallyNilpotent {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n)
    (hlocal : ∀ H : Subgroup G, Group.FG H → Group.IsNilpotent H) : IsPolycyclic G := by
  let := (hG.finiteCohomologicalDimension G).nilpotent_of_locallyNilpotent hlocal
  let := hG.1.fg
  exact isPolycyclic_of_finitelyGenerated_nilpotent G

end PolycyclicRecognition

end

end OAI
