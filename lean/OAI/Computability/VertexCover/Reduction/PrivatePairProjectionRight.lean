import Mathlib
import OAI.Computability.VertexCover.Reduction.CoordinateProductInvariant
import OAI.Computability.VertexCover.Reduction.RestrictionStarBudget

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

noncomputable def privateLocalKey (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d) (c : Fin Φ.M) :
    Option (Fin Φ.M) × Option (Fin Φ.u) × Option (Fin Φ.v) := by
  classical
  exact (if e ∈ internalPairs J then none else some c,
    if e ∈ internalPairs J ∧ e.1.1 = j then some (Φ.left c) else none,
    if e ∈ internalPairs J ∧ e.1.2 = j then some (Φ.right c) else none)

noncomputable def privateSeedKey (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (seed : Φ.Seeds d) :=
  fun e => Φ.privateLocalKey J j e (seed e)

noncomputable def privateSeedProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) : (Φ.restrictionForm d).Projection :=
  condition (B := Φ.restrictionBase d) (Φ.privateSeedKey J j)

noncomputable def privatePairProjection (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d) :
    (Φ.restrictionForm d).Projection :=
  coordinateCondition (Φ.restrictionBase d) ⟨0, Φ.M_pos⟩ e (Φ.privateLocalKey J j e)

theorem privatePairProjection_commute (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e b : PositionPair d) (f : Φ.RestrictionSpace d) :
    Φ.privatePairProjection J j e (Φ.privatePairProjection J j b f) =
      Φ.privatePairProjection J j b (Φ.privatePairProjection J j e f) := by
  by_cases heb : e = b
  · subst b; rfl
  · change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
      (conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ b (Φ.privateLocalKey J j b)) f) =
      conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ b (Φ.privateLocalKey J j b))
      (conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f)
    apply conditionMap_coordinate_commute
    exact heb

theorem privateSeedProjection_product (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (f : Φ.RestrictionSpace d) :
    Φ.privateSeedProjection J j
      (productMap (Φ.privatePairProjection J j) Finset.univ.toList f) =
      productMap (Φ.privatePairProjection J j) Finset.univ.toList f := by
  classical
  let F := productMap (Φ.privatePairProjection J j) Finset.univ.toList f
  change Φ.privateSeedProjection J j F = F
  funext seed
  apply conditionMap_of_invariant
  intro s t hst
  apply invariant_of_coordinate_invariant (Φ.privateLocalKey J j) F _ s t
    (fun e => congrFun hst e)
  intro e a c hc
  have he := productMap_fixed_of_mem (Φ.privatePairProjection J j)
    (Φ.privatePairProjection_commute J j) Finset.univ.toList e (by simp) f
  change Φ.privatePairProjection J j e F = F at he
  rw [← he]
  apply conditionMap_eq_of_key_eq
  simp only [coordinateKey, Function.update_idem, Function.update_self, hc]

theorem query_eq_questions_iff (Φ : LabelCover) {d : ℕ} (s t : Φ.Seeds d) (j : Fin d) :
    Φ.query s j = Φ.query t j ↔
      (∀ k (h : j < k), Φ.left (s ⟨(j,k),h⟩) = Φ.left (t ⟨(j,k),h⟩)) ∧
      (∀ k (h : k < j), Φ.right (s ⟨(k,j),h⟩) = Φ.right (t ⟨(k,j),h⟩)) := by
  constructor
  · intro h
    have hp := eq_of_heq (Sigma.mk.inj h).2
    exact ⟨fun k hk => congrFun (congrArg Prod.fst hp) ⟨k,hk⟩,
      fun k hk => congrFun (congrArg Prod.snd hp) ⟨k,hk⟩⟩
  · rintro ⟨hL,hR⟩
    exact Φ.query_eq_of_questions s t j hL hR

theorem privateSeedKey_eq_iff (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (s t : Φ.Seeds d) :
    Φ.privateSeedKey J j s = Φ.privateSeedKey J j t ↔
      (∀ e, e ∉ internalPairs J → s e = t e) ∧ Φ.query s j = Φ.query t j := by
  classical
  constructor
  · intro h
    have hs : ∀ e, e ∉ internalPairs J → s e = t e := by
      intro e he
      have hh := congrArg Prod.fst (congrFun h e)
      simpa only [privateSeedKey, privateLocalKey, ite_eq_right he, Option.some.injEq] using hh
    refine ⟨hs, (Φ.query_eq_questions_iff s t j).mpr ⟨?_, ?_⟩⟩
    · intro k hkj
      let e : PositionPair d := ⟨(j,k),hkj⟩
      by_cases he : e ∈ internalPairs J
      · have hh := congrArg (fun x => x.2.1) (congrFun h e)
        simpa [privateSeedKey, privateLocalKey, he, e] using hh
      · exact congrArg Φ.left (hs e he)
    · intro k hkj
      let e : PositionPair d := ⟨(k,j),hkj⟩
      by_cases he : e ∈ internalPairs J
      · have hh := congrArg (fun x => x.2.2) (congrFun h e)
        simpa [privateSeedKey, privateLocalKey, he, e] using hh
      · exact congrArg Φ.right (hs e he)
  · rintro ⟨hs,hq⟩
    obtain ⟨hL,hR⟩ := (Φ.query_eq_questions_iff s t j).mp hq
    funext e
    by_cases he : e ∈ internalPairs J
    · by_cases hlj : e.1.1 = j
      · have hrj : e.1.2 ≠ j := by have := e.2; rw [hlj] at this; exact ne_of_gt this
        have ht := hL e.1.2 (hlj ▸ e.2)
        have hp : (⟨(j,e.1.2), hlj ▸ e.2⟩ : PositionPair d) = e := by
          apply Subtype.ext; simp only [← hlj, Prod.mk.eta]
        rw [hp] at ht
        simp [privateSeedKey, privateLocalKey, he, hlj, hrj, ht]
      · by_cases hrj : e.1.2 = j
        · have ht := hR e.1.1 (hrj ▸ e.2)
          have hp : (⟨(e.1.1,j), hrj ▸ e.2⟩ : PositionPair d) = e := by
            apply Subtype.ext; simp only [← hrj, Prod.mk.eta]
          rw [hp] at ht
          simp [privateSeedKey, privateLocalKey, he, hlj, hrj, ht]
        · simp [privateSeedKey, privateLocalKey, he, hlj, hrj]
    · simp [privateSeedKey, privateLocalKey, he, hs e he]

theorem privatePairProjection_outside (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d) (he : e ∉ internalPairs J) :
    Φ.privatePairProjection J j e = ident := by
  classical
  apply EnergyForm.Projection.ext
  intro f
  funext seed
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f seed = f seed
  apply conditionMap_of_invariant
  intro s t hst
  obtain ⟨ho,hq⟩ := (coordinateKey_eq_iff ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e) s t).mp hst
  have heq : s e = t e := by
    have hh := congrArg Prod.fst hq
    simpa [privateLocalKey, he] using hh
  have hst' : s = t := by
    funext b
    by_cases hb : b = e
    · subst b; exact heq
    · exact ho b hb
  rw [hst']

theorem privatePairProjection_nonincident (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hL : e.1.1 ≠ j) (hR : e.1.2 ≠ j) :
    Φ.privatePairProjection J j e = Φ.seedProjection e := by
  apply EnergyForm.Projection.ext
  intro f
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f =
    conditionMap (fun seed : Φ.Seeds d => Function.update seed e ⟨0,Φ.M_pos⟩) f
  exact congrArg (fun L => L f) (conditionMap_congr
    (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
    (fun seed : Φ.Seeds d => Function.update seed e ⟨0,Φ.M_pos⟩) (fun s t => by
    simp [coordinateKey, privateLocalKey, he, hL, hR]))

theorem privatePairProjection_left (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hL : e.1.1 = j) :
    Φ.privatePairProjection J j e = Φ.oppositeProjection e.1.2 e := by
  classical
  have hR : e.1.2 ≠ j := by rw [← hL]; exact ne_of_gt e.2
  apply EnergyForm.Projection.ext
  intro f
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f =
    conditionMap (Φ.oppositePairKey e.1.2 e) f
  exact congrArg (fun L => L f) (conditionMap_congr
    (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
    (Φ.oppositePairKey e.1.2 e) (fun s t => by
    simp only [coordinateKey, privateLocalKey, oppositePairKey, he, hL,
      and_self, ite_true, hR, and_false, ite_false, Prod.mk.injEq,
      Option.some.injEq, true_and, and_true, ite_eq_right (Ne.symm hR)]
    constructor
    · rintro ⟨ho,hq⟩
      exact Prod.ext ho (congrArg Sum.inl hq)
    · intro h
      exact ⟨congrArg Prod.fst h, Sum.inl.inj (congrArg Prod.snd h)⟩))

theorem privatePairProjection_right (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : Fin d) (e : PositionPair d)
    (he : e ∈ internalPairs J) (hR : e.1.2 = j) :
    Φ.privatePairProjection J j e = Φ.oppositeProjection e.1.1 e := by
  classical
  have hL : e.1.1 ≠ j := by rw [← hR]; exact ne_of_lt e.2
  apply EnergyForm.Projection.ext
  intro f
  change conditionMap (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e)) f =
    conditionMap (Φ.oppositePairKey e.1.1 e) f
  exact congrArg (fun L => L f) (conditionMap_congr
    (coordinateKey ⟨0,Φ.M_pos⟩ e (Φ.privateLocalKey J j e))
    (Φ.oppositePairKey e.1.1 e) (fun s t => by
    simp only [coordinateKey, privateLocalKey, oppositePairKey, he, hL, hR,
      and_false, and_self, ite_false, ite_true, Prod.mk.injEq, Option.some.injEq,
      true_and]
    constructor
    · rintro ⟨ho,hq⟩
      exact Prod.ext ho (congrArg Sum.inr hq)
    · intro h
      exact ⟨congrArg Prod.fst h, Sum.inr.inj (congrArg Prod.snd h)⟩))

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
