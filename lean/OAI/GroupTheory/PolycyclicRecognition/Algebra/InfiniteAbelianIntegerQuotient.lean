import Mathlib.GroupTheory.FiniteAbelian.Basic

namespace OAI

/-! # An integer quotient of an infinite finitely generated abelian group

We use the structure theorem only to select one free coordinate. The resulting
map is an actual surjective group homomorphism to the integers.
-/

noncomputable section
namespace PolycyclicRecognition

theorem infinite_fg_abelian_integer_quotient (G : Type*)
    [CommGroup G] [Group.FG G] [Infinite G] :
    ∃ q : G →* Multiplicative ℤ, Function.Surjective q := by
  classical
  obtain ⟨ι, j, hι, hj, p, hp, e, ⟨f⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  let :=  hι
  let :=  hj
  have (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have hjne : Nonempty j := by
    by_contra h
    have : IsEmpty j := not_nonempty_iff.mp h
    have : Finite G := Finite.of_equiv _ f.toEquiv.symm
    exact not_finite G
  let a : j := Classical.choice hjne
  let q : G →* Multiplicative ℤ :=
    { toFun := fun g => (f g).1 a
      map_one' := by simp
      map_mul' := by intro x y; simp }
  refine ⟨q, fun z => ⟨f.symm (fun _ => z, 1), ?_⟩⟩
  simp [q]

end PolycyclicRecognition

end

end OAI
