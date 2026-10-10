import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteNormalRadical

namespace OAI

/-! # Finite-subgroup bounds and the quotient by the finite radical -/
noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type} [Group G] [Group Q]

theorem finite_subgroup_preimage (q : G →* Q) [Finite q.ker]
    (S : Subgroup Q) [Finite S] : Finite (S.comap q) := by
  let P := S.comap q
  let f : P →* S := (q.comp P.subtype).codRestrict S (fun p => p.property)
  let j : f.ker → q.ker := fun p => ⟨((p : P) : G),
    congrArg (fun s : S => (s : Q)) p.property⟩
  have hj : Function.Injective j := by
    intro p r hpr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => (z : G)) hpr
  let : Finite f.ker := Finite.of_injective j hj
  exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

theorem boundedFiniteSubgroupOrders_of_finite_kernel_quotient
    (q : G →* Q) (hq : Function.Surjective q) [Finite q.ker]
    (hb : HasBoundedFiniteSubgroupOrders G) : HasBoundedFiniteSubgroupOrders Q := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun S hS => ?_⟩
  let := hS
  let : Finite (S.comap q) := finite_subgroup_preimage q S
  let f : S.comap q →* S := (q.comp (S.comap q).subtype).codRestrict S (fun p => p.property)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨g, hg⟩ := hq s
    exact ⟨⟨g, by change q g ∈ S; rw [hg]; exact s.property⟩, Subtype.ext hg⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (hb (S.comap q) inferInstance)

theorem finite_normal_quotient_eq_bot (T : Subgroup G) [T.Normal] [Finite T]
    (hT : ∀ N : Subgroup G, N.Normal → Finite N → N ≤ T)
    (S : Subgroup (G ⧸ T)) [S.Normal] [Finite S] : S = ⊥ := by
  let q := QuotientGroup.mk' T
  let P := S.comap q
  let : Finite q.ker := by simpa only [q, QuotientGroup.ker_mk'] using (inferInstance : Finite T)
  let : Finite P := finite_subgroup_preimage q S
  have hP : P ≤ T := hT P inferInstance inferInstance
  apply eq_bot_iff.mpr
  intro s hs
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective T s
  have hgP : g ∈ P := by change q g ∈ S; rw [hg]; exact hs
  exact hg.symm.trans ((QuotientGroup.eq_one_iff g).mpr (hP hgP))

end PolycyclicRecognition

end

end OAI
