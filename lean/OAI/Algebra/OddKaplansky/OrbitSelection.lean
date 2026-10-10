import OAI.Algebra.OddKaplansky.WeightedProjection

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.OrbitSelection
noncomputable section
open scoped Classical BigOperators
variable {H : Type portUniverse1} {A : Type portUniverse2} [Group H] [sectionInstance25 : Fintype H] [sectionInstance26 : Fintype A] [MulAction H A]
variable (good : A → Prop)
abbrev Rep := {q : MulAction.orbitRel.Quotient H A // ∃ a : A, (Quotient.mk'' a : MulAction.orbitRel.Quotient H A) = q ∧ good a}
instance : Fintype (Rep (H := H) good) := Fintype.ofFinite _

def representative (r : Rep (H := H) good) : A := r.property.choose
lemma representative_spec
    {H : Type contextUniverse1}
    {A : Type contextUniverse2}
    [contextInstance2 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [Fintype.{contextUniverse2} A]
    [@MulAction.{contextUniverse1, contextUniverse2} H A (@DivInvMonoid.toMonoid.{contextUniverse1} H (@Group.toDivInvMonoid.{contextUniverse1} H contextInstance2))]
    (good : A → Prop) (r : Rep (H := H) good) :
    (Quotient.mk'' (representative good r) : MulAction.orbitRel.Quotient H A) = r.val ∧ good (representative good r) := r.property.choose_spec

lemma cover (a : A) (ha : good a) : ∃ r : Rep (H := H) good, ∃ h : H, h • representative good r = a := by
  let r : Rep (H := H) good := ⟨Quotient.mk'' a,⟨a,rfl,ha⟩⟩
  refine ⟨r,?_⟩
  have hh : (Quotient.mk'' a : MulAction.orbitRel.Quotient H A) = Quotient.mk'' (representative good r) :=
    (representative_spec good r).1.symm
  exact Quotient.exact hh

lemma card_good : Fintype.card {a : A // good a} ≤ Fintype.card (Rep (H := H) good) * Fintype.card H := by
  choose r h he using fun a : {a : A // good a} => cover (H := H) good a.val a.property
  have hi : Function.Injective (fun a => (r a,h a)) := by
    intro a b hab
    apply Subtype.ext
    rw [← he a,← he b]
    exact congrArg (fun z : Rep (H := H) good × H => z.2 • representative good z.1) hab
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective _ hi

lemma orbit_injective (hfree : ∀ a, good a → ∀ g : H, g • a = a → g = 1) :
    Function.Injective (fun r : Rep (H := H) good × H => r.2 • representative good r.1) := by
  rintro ⟨r,g⟩ ⟨s,h⟩ he
  have hrs : r = s := by
    apply Subtype.ext
    have hh := congrArg (Quotient.mk'' : A → MulAction.orbitRel.Quotient H A) he
    simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq,(representative_spec good r).1,(representative_spec good s).1] using hh
  subst s
  have hh : h⁻¹*g = 1 := by
    apply hfree (representative good r) (representative_spec good r).2
    simpa only [mul_smul,inv_smul_smul] using congrArg (fun a : A => h⁻¹ • a) he
  have hgh : g = h := (inv_mul_eq_one.mp hh).symm
  subst g
  rfl
end
end OddKaplansky.OrbitSelection

end

end OAI
