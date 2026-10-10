import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralLayerAscendingBase
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AscendingBaseTransport

namespace OAI

/-! # Ascending bases lift from a nilpotent abelianization

This proves the lifting step used in Kropholler--Martínez-Pérez--Nucinkis,
J. reine angew. Math. 637 (2009), Lemma 2.3. The last lower-central subgroup
is central. Commutators of quotient lifts give its stable finite base, and
finite lift errors are absorbed before continuing by induction.
-/

noncomputable section
namespace PolycyclicRecognition

private theorem ascending_base_of_commutator_eq_bot
    {G : Type} [Group G] (hc : commutator G = ⊥) (α : MulAut G)
    (hα : HasFinitelyGeneratedAscendingBase (characteristicQuotientAut (commutator G) α)) :
    HasFinitelyGeneratedAscendingBase α := by
  let q := QuotientGroup.mk' (commutator G)
  have hq : Function.Bijective q := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    apply q.ker_eq_bot_iff.mp
    exact (QuotientGroup.ker_mk' _).trans hc
  let e := MulEquiv.ofBijective q hq
  exact hα.of_equiv e α (characteristicQuotientAut (commutator G) α) (fun _ => rfl)

private theorem nilpotent_ascending_base_induction (c : ℕ) :
    ∀ (G : Type) [Group G] [Group.IsNilpotent G],
      (⊤ : Subgroup G).lowerCentralSeries (c + 1) = ⊥ →
      ∀ α : MulAut G,
        HasFinitelyGeneratedAscendingBase (characteristicQuotientAut (commutator G) α) →
        HasFinitelyGeneratedAscendingBase α := by
  induction c with
  | zero =>
    intro G _ _ hc α hα
    exact ascending_base_of_commutator_eq_bot hc α hα
  | succ c ih =>
    intro G _ _ hc α hα
    let N := (⊤ : Subgroup G).lowerCentralSeries (c + 1)
    let q := QuotientGroup.mk' N
    let β := characteristicQuotientAut N α
    have hcentral : N ≤ Subgroup.center G :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hc
    have hQ : (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries (c + 1) = ⊥ := by
      have h := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) q (c + 1)
      rw [Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at h
      rw [← h]
      change N.map (QuotientGroup.mk' N) = ⊥
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hβab := ascendingBase_abelianization_of_surjective q
      (QuotientGroup.mk'_surjective N) α β (fun _ => rfl) hα
    obtain ⟨P, hPfg, hPstable, hPcover⟩ := ih (G ⧸ N) hQ β hβab
    exact exists_ascending_base_of_central_lowerCentral_quotient N c rfl hcentral
      α P hPfg hPstable hPcover

theorem nilpotent_ascending_base_of_abelianization
    {G : Type} [Group G] [Group.IsNilpotent G] (α : MulAut G)
    (hα : HasFinitelyGeneratedAscendingBase (characteristicQuotientAut (commutator G) α)) :
    HasFinitelyGeneratedAscendingBase α := by
  obtain ⟨c, hc⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := G)).mp inferInstance
  apply nilpotent_ascending_base_induction c G ?_ α hα
  apply eq_bot_iff.mpr
  exact ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ c)).trans hc.le

end PolycyclicRecognition

end

end OAI
