import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DimensionFromRegularCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexFiniteness

namespace OAI

/-! # A common duality dimension for the nilpotent exhaustion -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_duality_dimension
    (hG : HasFiniteIntegralCohomologicalDimension G)
    (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) :
    ∃ d, IsIntegralPoincareDualityGroup H d ∧
      ∀ L : Subgroup G, L.FG → H ≤ L → IsIntegralPoincareDualityGroup L d := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨d, hd⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (hG.subgroup H).torsionFree
  refine ⟨d, hd, ?_⟩
  intro L hL hHL
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  obtain ⟨e, he⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (hG.subgroup L).torsionFree
  let := nilpotent_rootCore_finiteIndex hG H hroot L hL
  have hHe : IsIntegralPoincareDualityGroup H e :=
    (he.finiteIndex_subgroup (H.subgroupOf L)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hHL)
  have hde : d = e := hd.dimension_unique hHe
  exact hde ▸ he

theorem exists_nilpotent_duality_exhaustion_finiteIndex [Countable G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∃ S : ℕ → Subgroup G,
      Monotone S ∧ (∀ n, (S n).FG) ∧ (∀ g, ∃ n, g ∈ S n) ∧
      (∀ n, IsIntegralPoincareDualityGroup (S n) d) ∧
      (∀ i j, ((S i).subgroupOf (S j)).FiniteIndex) := by
  classical
  obtain ⟨H, hH, hroot⟩ := nilpotent_exists_fg_subgroup_containing_powers hG
  obtain ⟨d, _, hd⟩ := nilpotent_rootCore_duality_dimension hG H hH hroot
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let T (n : ℕ) : Set G := Set.range (fun i : Fin n => e i)
  let S (n : ℕ) := H ⊔ Subgroup.closure (T n)
  have hS (n : ℕ) : (S n).FG :=
    hH.sup ((Subgroup.fg_iff _).mpr ⟨T n, rfl, Set.finite_range _⟩)
  refine ⟨d, S, ?_, hS, ?_, (fun n => hd (S n) (hS n) le_sup_left), ?_⟩
  · intro i j hij
    apply sup_le_sup_left
    apply Subgroup.closure_mono
    rintro g ⟨k, rfl⟩
    exact ⟨⟨k, k.isLt.trans_le hij⟩, rfl⟩
  · intro g
    obtain ⟨n, rfl⟩ := he g
    refine ⟨n + 1, (show Subgroup.closure (T (n + 1)) ≤ S (n + 1) from le_sup_right) ?_⟩
    exact Subgroup.subset_closure ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  · intro i j
    apply nilpotent_rootCore_finiteIndex hG (S i) _ (S j) (hS j)
    intro g
    obtain ⟨n, hn, hgn⟩ := hroot g
    exact ⟨n, hn, (show H ≤ S i from le_sup_left) hgn⟩

theorem exists_nilpotent_duality_exhaustion [Countable G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∃ S : ℕ → Subgroup G,
      Monotone S ∧ (∀ n, (S n).FG) ∧ (∀ g, ∃ n, g ∈ S n) ∧
      (∀ n, IsIntegralPoincareDualityGroup (S n) d) := by
  obtain ⟨d, S, hS, hfg, hcover, hd, _⟩ :=
    exists_nilpotent_duality_exhaustion_finiteIndex hG
  exact ⟨d, S, hS, hfg, hcover, hd⟩

end PolycyclicRecognition

end

end OAI
