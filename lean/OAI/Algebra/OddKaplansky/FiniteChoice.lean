import OAI.Algebra.OddKaplansky.QuadraticTower

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9

section
namespace OddKaplansky.FiniteChoice
noncomputable section
open scoped Classical
variable {A : Type portUniverse1} {B : Type portUniverse2}
def orderedIndex (A : Type portUniverse3) [LinearOrder A] [Fintype A] : A ≃ Fin (Fintype.card A) :=
  (Fintype.orderIsoFinOfCardEq A rfl).symm.toEquiv
def table [LinearOrder A] [Fintype A] (f : A → B) : List B :=
  List.ofFn (fun i => f ((orderedIndex A).symm i))
lemma table_injective [LinearOrder A] [Fintype A] : Function.Injective (table (A := A) (B := B)) := by
  intro f g he
  have hh := List.ofFn_injective he
  funext a
  simpa only [Equiv.symm_apply_apply] using congrFun hh (orderedIndex A a)
@[instance_reducible]
def functionOrder (A : Type portUniverse4) (B : Type portUniverse5) [Fintype A] [LinearOrder A] [LinearOrder B] : LinearOrder (A → B) :=
  LinearOrder.lift' table table_injective
@[instance_reducible]
def tupleOrder (A : Type portUniverse6) (B : Type portUniverse7) [LinearOrder A] [LinearOrder B] : LinearOrder (A×B) :=
  LinearOrder.lift' (fun a : A×B => toLex a) (fun _ _ h => h)
@[instance_reducible]
def residueOrder (n : ℕ) [NeZero n] : LinearOrder (ZMod n) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective n)
@[instance_reducible]
def multiplicativeOrder [LinearOrder A] : LinearOrder (Multiplicative A) :=
  LinearOrder.lift' Multiplicative.toAdd Multiplicative.toAdd.injective
lemma exists_primitive (F : Type portUniverse8) [Field F] [Fintype F] : ∃ ζ : F, IsPrimitiveRoot ζ (Fintype.card F-1) := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨u,?_⟩
  rw [← Fintype.card_units F,← Nat.card_eq_fintype_card,← hu]
  simpa only [orderOf_units] using IsPrimitiveRoot.orderOf (u : F)
variable [Fintype A] [sectionInstance1 : LinearOrder A] (P : A → Prop) (hP : ∃ a, P a)
def candidates : Finset A := Finset.univ.filter P
lemma candidates_nonempty
    {A : Type contextUniverse1}
    [Fintype.{contextUniverse1} A]
    [LinearOrder.{contextUniverse1} A]
    (P : A → Prop)
    (hP : @Exists.{contextUniverse1 + 1} A fun a => P a) : (candidates P).Nonempty := by
  obtain ⟨a,ha⟩ := hP
  exact ⟨a,by simp [candidates,ha]⟩
def first : A := (candidates P).min' (candidates_nonempty P hP)
lemma first_spec : P (first P hP) := by
  have h := Finset.min'_mem (candidates P) (candidates_nonempty P hP)
  simpa only [first,candidates,Finset.mem_filter,Finset.mem_univ,true_and] using h
lemma first_le (a : A) (ha : P a) : first P hP ≤ a :=
  Finset.min'_le _ _ (by simp [candidates,ha])
variable (F : Type portUniverse9) [Field F] [Fintype F] [LinearOrder F]
def primitive : F := first (fun ζ : F => IsPrimitiveRoot ζ (Fintype.card F-1)) (exists_primitive F)
lemma primitive_spec : IsPrimitiveRoot (primitive F) (Fintype.card F-1) := by unfold primitive; exact first_spec (fun ζ : F => IsPrimitiveRoot ζ (Fintype.card F-1)) (exists_primitive F)
lemma primitive_le (ζ : F) (hζ : IsPrimitiveRoot ζ (Fintype.card F-1)) : primitive F≤ζ := by unfold primitive; exact first_le (fun ζ : F => IsPrimitiveRoot ζ (Fintype.card F-1)) (exists_primitive F) ζ hζ

end
end OddKaplansky.FiniteChoice

end

end OAI
