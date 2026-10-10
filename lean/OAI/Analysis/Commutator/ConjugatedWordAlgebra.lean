import Mathlib
import OAI.Analysis.Commutator.PartialUnitaryHom
import OAI.Analysis.Commutator.PartialWordReindex

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {B J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def signPower (c : Bool) : ℤ := if c then 1 else -1

def leftUnitary (u : unitary B) (c : Bool) : unitary B := if c then 1 else u

def transition (c d : Bool) : Slot Bool := if c=d then none else some (some c)

def front (color : J → Bool) (σ : Bool) : List J → Bool
  | [] => σ
  | a::_ => color a

def encode (color : J → Bool) (σ : Bool) : List J → List (Letter J Bool)
  | [] => []
  | a::l => (a,transition (color a) (front color σ l))::encode color σ l

omit [PartialOrder B] [StarOrderedRing B] in
lemma transition_power (u : unitary B) (c d : Bool) :
    slotPower signPower (PartialUnitary.ofUnitary u) (transition c d)=
      star (leftUnitary u c:B)*(leftUnitary u d:B) := by
  cases c <;> cases d <;>
    simp [transition,signPower,slotPower,leftUnitary,
      PartialUnitary.ofUnitary_power_one,PartialUnitary.ofUnitary_power_neg_one,
      u.property.1]

@[simp] lemma encode_length (color : J → Bool) (σ : Bool) (l : List J) :
    (encode color σ l).length=l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [encode,ih]

lemma encode_ne_nil (color : J → Bool) (σ : Bool) {l : List J} (hl : l≠[]) :
    encode color σ l≠[] := by
  intro he
  have hh := congrArg List.length he
  simp only [encode_length,List.length_nil,List.length_eq_zero_iff] at hh
  exact hl hh

lemma encode_valid (color : J → Bool) (σ : Bool) {l : List J}
    (hl : l.IsChain (fun a b => color a≠color b)) : Valid (encode color σ l) := by
  induction l with
  | nil =>
    intro s i t he ht
    have hh := congrArg List.length he
    simp only [encode,List.length_nil,List.length_append,List.length_cons] at hh
    omega
  | cons a l ih =>
    rw [encode,valid_cons_iff]
    refine ⟨ih hl.tail,?_⟩
    intro hne
    cases l with
    | nil => exact (hne rfl).elim
    | cons b l =>
      have hab := (List.isChain_cons_cons.mp hl).1
      refine ⟨color a,?_⟩
      change (if color a=color b then (none : Slot Bool) else some (some (color a)))=some (some (color a))
      exact ite_eq_right hab

omit [PartialOrder B] [StarOrderedRing B] in
lemma word_encode (u : unitary B) (x : J → B) (color : J → Bool)
    (σ : Bool) (l : List J) :
    word x signPower (PartialUnitary.ofUnitary u) (encode color σ l)=
      star (leftUnitary u (front color σ l):B)*
        (l.map (fun a => (leftUnitary u (color a):B)*x a*star (leftUnitary u (color a):B))).prod*
        (leftUnitary u σ:B) := by
  induction l with
  | nil => simp only [encode,word_nil,List.map_nil,List.prod_nil,front,mul_one]; exact (leftUnitary u σ).property.1.symm
  | cons a l ih =>
    simp only [encode,word_cons,letter,transition_power,ih,List.map_cons,List.prod_cons,front]
    let v := leftUnitary u (color a)
    let w := leftUnitary u (front color σ l)
    let z := (l.map (fun a => (leftUnitary u (color a):B)*x a*star (leftUnitary u (color a):B))).prod
    change x a*(star (v:B)*(w:B))*(star (w:B)*z*(leftUnitary u σ:B))=
      star (v:B)*((v:B)*x a*star (v:B)*z)*(leftUnitary u σ:B)
    calc
      _=x a*star (v:B)*((w:B)*star (w:B))*z*(leftUnitary u σ:B) := by noncomm_ring
      _=x a*star (v:B)*z*(leftUnitary u σ:B) := by rw [w.property.2,mul_one]
      _=(star (v:B)*(v:B))*(x a*star (v:B)*z)*(leftUnitary u σ:B) := by rw [v.property.1,one_mul]
      _=_ := by noncomm_ring

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
