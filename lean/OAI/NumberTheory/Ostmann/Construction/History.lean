import Mathlib
import OAI.NumberTheory.Ostmann.Arithmetic.ReversalCoprimality

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

inductive SlotRole
  | bulk
  | top
  | compensation (level : ℕ)
  deriving DecidableEq

structure SmallSlot where
  role : SlotRole
  value : ℕ
  
  origin : ℕ := 0
  deriving DecidableEq

structure State where
  frequency : ℤ
  giantPlus : ℕ
  giantMinus : ℕ
  small : List SmallSlot
  deriving DecidableEq

namespace State

def values (a : State) : List ℕ := a.giantPlus :: a.giantMinus :: a.small.map SmallSlot.value

def product (a : State) : ℕ := a.values.prod

def Coprime (a : State) (outside : List ℕ) : Prop :=
  (a.values ++ outside).Pairwise Nat.Coprime

def Positive (a : State) : Prop := ∀ v ∈ a.values, 0 < v

def PrimeSmall (a : State) : Prop := ∀ v ∈ a.small, Nat.Prime v.value

def TemplateAt (l : ℕ) (a : State) : Prop :=
  ∀ q ∈ a.small, ∀ j, q.role = .compensation j → l < j

theorem templateAt_restore {l : ℕ} {a child : State} {u inherited : List SmallSlot}
    (ha : a.TemplateAt (l+1)) (hinherited : ∀ q ∈ inherited, q ∈ a.small)
    (hu : ∀ q ∈ u, q.role = .compensation (l+1))
    (hchild : child.small = u ++ inherited) : child.TemplateAt l := by
  intro q hq j hrole
  rw [hchild, List.mem_append] at hq
  rcases hq with hq | hq
  · have hj := (hu q hq).symm.trans hrole
    injection hj with hj
    omega
  · have hj := ha q (hinherited q hq) j hrole
    omega

end State

inductive History : ℕ → Type
  | leaf (state : State) : History 0
  | node {l : ℕ} (state : State) (pivot : ℕ)
      (compensation plusSmall minusSmall : List SmallSlot)
      (left right : History l) : History (l+1)

namespace History

def root : {l : ℕ} → History l → State
  | _, .leaf a => a
  | _, .node a _ _ _ _ _ _ => a

def frequencies : {l : ℕ} → History l → List ℤ
  | _, .leaf a => [a.frequency]
  | _, .node a _ _ _ _ left right => a.frequency :: (left.frequencies ++ right.frequencies)

def internalOccurrences : {l : ℕ} → History l → List SmallSlot
  | _, .leaf _ => []
  | _, .node _ _ u _ _ left right => u ++ left.internalOccurrences ++ right.internalOccurrences

def leafStates : {l : ℕ} → History l → List State
  | _, .leaf a => [a]
  | _, .node _ _ _ _ _ left right => left.leafStates ++ right.leafStates

@[simp] theorem leafStates_length {l : ℕ} (h : History l) : h.leafStates.length = 2^l := by
  induction h with
  | leaf a => simp [leafStates]
  | @node l a p u hp hm left right ihl ihr =>
      simp only [leafStates, List.length_append, ihl, ihr, pow_succ]
      omega

@[simp] theorem frequencies_length {l : ℕ} (h : History l) :
    h.frequencies.length + 1 = 2^(l+1) := by
  induction h with
  | leaf a => norm_num [frequencies]
  | @node l a p u hp hm left right ihl ihr =>
      simp only [frequencies, List.length_cons, List.length_append, pow_succ] at *
      omega

def GiantUnits {l : ℕ} (h : History l) : Prop :=
  ∀ v ∈ h.frequencies,
    Nat.Coprime h.root.giantPlus v.natAbs ∧ Nat.Coprime h.root.giantMinus v.natAbs

def Supported (V : ℕ → ℕ) (outside : List ℕ) : {l : ℕ} → History l → Prop
  | l, h =>
    h.root.Positive ∧ h.root.PrimeSmall ∧ h.root.TemplateAt l ∧ h.root.Coprime outside ∧
    h.root.frequency ≠ 0 ∧ h.root.frequency.natAbs ≤ V l ∧ h.GiantUnits ∧
    match h with
    | .leaf _ => True
    | .node a p u hp hm left right =>
      0 < p ∧
      (∀ q ∈ u, q.role = .compensation l) ∧
      a.small.Perm (hp ++ hm) ∧
      left.root.giantPlus = p ∧ right.root.giantPlus = p ∧
      left.root.giantMinus = a.giantPlus ∧ right.root.giantMinus = a.giantMinus ∧
      left.root.small.Perm (u ++ hp) ∧ right.root.small.Perm (u ++ hm) ∧
      Arithmetic.reversalNumerator left.root.frequency right.root.frequency
          ((a.giantPlus * (hp.map SmallSlot.value).prod : ℕ) : ℤ)
          ((a.giantMinus * (hm.map SmallSlot.value).prod : ℕ) : ℤ) =
        a.frequency * ((u.map SmallSlot.value).prod : ℤ) * (p : ℤ) ∧
      Supported V outside left ∧ Supported V outside right
termination_by l _ => l

def weight (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) : {l : ℕ} → History l → ℂ
  | _, .leaf a => base a
  | _, .node _ p u _ _ left right =>
      (((u.map SmallSlot.value).prod : ℂ) * (φ (Real.log p - G) : ℂ)) *
        weight base φ G left * conj (weight base φ G right)

def supportedWeight (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) : ℂ := by
  classical
  exact if h.Supported V outside then h.weight base φ G else 0

@[simp] theorem supportedWeight_of_not_supported (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l)
    (hs : ¬ h.Supported V outside) : h.supportedWeight V outside base φ G = 0 := by
  simp [supportedWeight, hs]

theorem supported_template {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : h.root.TemplateAt l := by
  rw [Supported.eq_def] at hs
  exact hs.2.2.1

theorem supported_root_frequency_ne_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : h.root.frequency ≠ 0 := by
  rw [Supported.eq_def] at hs
  exact hs.2.2.2.2.1

theorem supported_root_coprime {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : h.root.Coprime outside := by
  rw [Supported.eq_def] at hs
  exact hs.2.2.2.1

theorem supported_root_frequency_bound {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : h.root.frequency.natAbs ≤ V l := by
  rw [Supported.eq_def] at hs
  exact hs.2.2.2.2.2.1

theorem supported_root_positive {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : h.root.Positive := by
  rw [Supported.eq_def] at hs
  exact hs.1

theorem supported_left {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    left.Supported V outside := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩
  exact hl

theorem supported_right {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    right.Supported V outside := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr⟩
  exact hr

theorem supported_pivot_pos {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) : 0 < p := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, hpos, _⟩
  exact hpos

theorem supported_compensation_roles {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    ∀ q ∈ u, q.role = .compensation (l+1) := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, hroles, _⟩
  exact hroles

theorem supported_compensation_product_pos {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    0 < (u.map SmallSlot.value).prod := by
  have hleft := supported_root_positive (supported_left hs)
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsmall, _⟩
  apply List.prod_pos
  intro q hq
  obtain ⟨slot, hslot, rfl⟩ := List.mem_map.mp hq
  apply hleft
  simp only [State.values, List.mem_cons, List.mem_map]
  exact Or.inr (Or.inr ⟨slot, hsmall.mem_iff.mpr (List.mem_append_left hp hslot), rfl⟩)

theorem supported_small_split {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    a.small.Perm (hp ++ hm) := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, hsmall, _⟩
  exact hsmall

theorem supported_child_giants {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    left.root.giantPlus=p ∧ right.root.giantPlus=p ∧
      left.root.giantMinus=a.giantPlus ∧ right.root.giantMinus=a.giantMinus := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, hlp, hrp, hlm, hrm, _⟩
  exact ⟨hlp,hrp,hlm,hrm⟩

theorem supported_child_small {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    left.root.small.Perm (u++hp) ∧ right.root.small.Perm (u++hm) := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hl,hr, _⟩
  exact ⟨hl,hr⟩

theorem supported_small_product_split {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (a.small.map SmallSlot.value).prod =
      (hp.map SmallSlot.value).prod * (hm.map SmallSlot.value).prod := by
  calc
    _ = ((hp++hm).map SmallSlot.value).prod :=
      ((supported_small_split hs).map SmallSlot.value).prod_eq
    _ = _ := by rw [List.map_append, List.prod_append]

theorem supported_child_small_products {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (left.root.small.map SmallSlot.value).prod =
        (u.map SmallSlot.value).prod*(hp.map SmallSlot.value).prod ∧
      (right.root.small.map SmallSlot.value).prod =
        (u.map SmallSlot.value).prod*(hm.map SmallSlot.value).prod := by
  obtain ⟨hl,hr⟩ := supported_child_small hs
  constructor
  · exact (hl.map SmallSlot.value).prod_eq.trans (by rw [List.map_append,List.prod_append])
  · exact (hr.map SmallSlot.value).prod_eq.trans (by rw [List.map_append,List.prod_append])

theorem supported_reversal {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    Arithmetic.reversalNumerator left.root.frequency right.root.frequency
        ((a.giantPlus * (hp.map SmallSlot.value).prod : ℕ) : ℤ)
        ((a.giantMinus * (hm.map SmallSlot.value).prod : ℕ) : ℤ) =
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) * (p : ℤ) := by
  rw [Supported] at hs
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq, _, _⟩
  exact heq

end History
end Ostmann.Construction

end

end OAI
