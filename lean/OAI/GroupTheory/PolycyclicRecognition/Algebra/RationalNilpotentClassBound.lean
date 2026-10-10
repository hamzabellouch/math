import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentFiniteTailBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyNilpotentRationalEndgame
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DirectedLowerCentral

namespace OAI

/-! # A nilpotency-class bound allowing finite torsion -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Countable G]

theorem rational_nilpotencyClass_le [Group.IsNilpotent G] (d b : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : ∀ T : Subgroup G, Finite T → Nat.card T ≤ b) :
    Group.nilpotencyClass G ≤ 2 * (d + 1) + b := by
  let hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H := fun _ _ => inferInstance
  let T := locallyNilpotentTorsionSubgroup hlocal
  obtain ⟨hTf, hQ, hQd⟩ := locallyNilpotent_mod_finite_torsion d hd ⟨b, hb⟩ hlocal
  let : Finite T := hTf
  let : Group.IsNilpotent (G ⧸ T) := hQ
  let : HasProjectiveDimensionLE (trivialIntegral (G ⧸ T)) (d + 1) := hQd
  exact (nilpotencyClass_le_quotient_add_finite_kernel T).trans
    (Nat.add_le_add (nilpotencyClass_le_twice_cohomologicalDimension (d + 1)) (hb T inferInstance))

theorem exists_maximal_nilpotent_normal_of_rational_dimension (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F := by
  obtain ⟨b, hb⟩ := hb
  have hclass (N : Subgroup G) [Group.IsNilpotent N] :
      Group.nilpotencyClass N ≤ 2 * (d + 1) + b := by
    apply rational_nilpotencyClass_le d b (RationalQuotient.rational_dimension_subgroup N d hd)
    intro T hT
    let := hT
    let e := T.equivMapOfInjective N.subtype Subtype.val_injective
    let : Finite (T.map N.subtype) := Finite.of_equiv T e.toEquiv
    simpa only [Nat.card_congr e.toEquiv] using hb (T.map N.subtype) inferInstance
  let P : Set (Subgroup G) := {N | N.Normal ∧ Group.IsNilpotent N}
  obtain ⟨F, hF, hmax⟩ := zorn_le₀ P (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, ⟨inferInstance, inferInstance⟩, by simp⟩
    · have hn : (sSup C).Normal := Subgroup.sSup_normal C (fun N hN => (hC hN).1)
      have hnil : Group.IsNilpotent (sSup C : Subgroup G) := by
        apply (Subgroup.isNilpotent_iff_lowerCentralSeries (sSup C)).mpr
        refine ⟨2 * (d + 1) + b, sSup_lowerCentralSeries_eq_bot C hne hchain.directedOn _ ?_⟩
        intro N hN
        let := (hC hN).2
        exact Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le (hclass N)
      exact ⟨sSup C, ⟨hn, hnil⟩, fun N hN => le_sSup hN⟩)
  exact ⟨F, hF.1, hF.2, fun N hn hnil hFN => le_antisymm (hmax ⟨hn, hnil⟩ hFN) hFN⟩

end PolycyclicRecognition

end

end OAI
