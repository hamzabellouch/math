import OAI.GroupTheory.PolycyclicRecognition.Geometry.CentralRootGenerators

namespace OAI

/-! # A finitely generated subgroup containing a power of every element

Central-quotient induction uses the uniform abelian rank bound in all
quotients. The chosen subgroup is an actual finite generating core; the
statement does not assert finite generation of the original nilpotent group.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

theorem nilpotent_quotient_exists_fg_subgroup_containing_powers
    {G Q : Type} [Group G] [Group.IsNilpotent G] [Group Q] [Group.IsNilpotent Q]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (q : G →* Q) (hq : Function.Surjective q) (hQ : HasNoNontrivialTorsion Q) :
    ∃ H : Subgroup Q, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  apply Group.nilpotent_center_quotient_ind Q
    (P := fun K _ _ => ∀ f : G →* K, Function.Surjective f → HasNoNontrivialTorsion K →
      ∃ H : Subgroup K, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) ?_ ?_ q hq hQ
  · intro K _ _ _ _ _
    exact ⟨⊥, Subgroup.FG.bot, fun g => ⟨1, by omega, by simp [Subsingleton.elim g 1]⟩⟩
  · intro K _ _ ih f hf hK
    have hrank := nilpotent_quotient_abelian_subgroup_rank_le d f hf (Subgroup.center K)
    have hfinite : Module.Finite ℚ (RationalAbelianSpace (Subgroup.center K)) := by
      apply Module.rank_lt_aleph0_iff.mp
      rw [rationalAbelianSpace_rank]
      exact hrank.trans_lt Cardinal.natCast_lt_aleph0
    let := hfinite
    have hZ := abelian_exists_fg_subgroup_containing_powers
      (hK.of_injective (Subgroup.center K).subtype Subtype.val_injective)
    let qK := QuotientGroup.mk' (Subgroup.center K)
    have hquot := ih (qK.comp f) ((QuotientGroup.mk'_surjective _).comp hf)
      (nilpotent_centerQuotient_torsionFree hK)
    exact exists_fg_subgroup_containing_powers_of_center hZ hquot

theorem nilpotent_exists_fg_subgroup_containing_powers
    {G : Type} [Group G] [Group.IsNilpotent G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  have htf := hG.torsionFree
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact nilpotent_quotient_exists_fg_subgroup_containing_powers d (MonoidHom.id G)
    Function.surjective_id htf

end PolycyclicRecognition

end

end OAI
