import Mathlib

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

def switchFun {d : ℕ} (ξ : Card d → Bool) (x : Card (d + 1)) : Card (d + 1) :=
  Fin.cons (Bool.xor (x 0) (ξ (Fin.tail x))) (Fin.tail x)

theorem switchFun_involutive {d : ℕ} (ξ : Card d → Bool) :
    Function.Involutive (switchFun ξ) := by
  intro x
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [switchFun, Fin.cons_zero, Fin.tail_cons]
    cases x 0 <;> cases ξ (Fin.tail x) <;> rfl
  · simp [switchFun, Fin.tail]

def pairSwitch {d : ℕ} (ξ : Card d → Bool) : Equiv.Perm (Card (d + 1)) :=
  { toFun := switchFun ξ
    invFun := switchFun ξ
    left_inv := switchFun_involutive ξ
    right_inv := switchFun_involutive ξ }

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def orbitSet (p : Equiv.Perm α) (x : α) : Finset α :=
  Finset.univ.filter (p.SameCycle x)

end Thorp

namespace Thorp.RoutingNetwork
open scoped BigOperators
open Filter
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
variable {A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (α)) (S : Finset (α)) :=
  {C : Finset (α) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

end Thorp.RoutingNetwork

namespace Thorp
open scoped BigOperators
open Filter

def cardSplit : (r s : ℕ) → Card (s+r) ≃ Card r × Card s
  | 0, s =>
    { toFun := fun x => ((fun i => Fin.elim0 i), x)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  | r+1, s =>
    { toFun := fun x => (Fin.cons (x 0) ((cardSplit r s (Fin.tail x)).1),
        (cardSplit r s (Fin.tail x)).2)
      invFun := fun x => Fin.cons (x.1 0) ((cardSplit r s).symm (Fin.tail x.1,x.2))
      left_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta, Equiv.symm_apply_apply, Fin.cons_self_tail]
      right_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail] }

def assembleBits : (r s : ℕ) → (Card r × SwitchIndex s → Bool) →
    (Card s × SwitchIndex r → Bool) → SwitchIndex (s+r) → Bool
  | 0, _, lo, _, i => lo ((fun j => Fin.elim0 j), i)
  | r+1, s, _, hi, Sum.inl y => hi ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
  | r+1, s, lo, hi, Sum.inr (b,i) => assembleBits r s
      (fun j => lo (Fin.cons b j.1,j.2)) (fun j => hi (j.1,Sum.inr (b,j.2))) i


section
variable {β : Type*} [Fintype β] [DecidableEq β]

def pairLayer (ξ : β → Bool) : Equiv.Perm (Bool × β) where
  toFun x := (Bool.xor x.1 (ξ x.2),x.2)
  invFun x := (Bool.xor x.1 (ξ x.2),x.2)
  left_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl
  right_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl

end

def coinStepEquiv (d : ℕ) : (SwitchIndex (d+1) → Bool) ≃
    ((SwitchIndex d → Bool) × (SwitchIndex d → Bool)) × (Card d → Bool) where
  toFun ω := ((fun i => ω (Sum.inr (false,i)),fun i => ω (Sum.inr (true,i))),
    fun x => ω (Sum.inl x))
  invFun ω := Sum.elim ω.2 (fun bi => if bi.1 then ω.1.2 bi.2 else ω.1.1 bi.2)
  left_inv ω := by
    funext i
    cases i with
    | inl x => rfl
    | inr bi => cases bi with | mk b i => cases b <;> rfl
  right_inv ω := by
    rcases ω with ⟨⟨ω₀,ω₁⟩,ξ⟩
    rfl

def headTailEquiv (d : ℕ) : Card (d+1) ≃ Bool × Card d :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm

end Thorp

namespace Thorp.CycleColoring
open scoped BigOperators
open Filter
variable {α : Type*} [Fintype α] [DecidableEq α]

def alternatingPerm (p : Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := if x.1 then (false,p x.2) else (true,x.2)
  invFun x := if x.1 then (false,x.2) else (true,p.symm x.2)
  left_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp
  right_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp

end Thorp.CycleColoring

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

def required (x : ι → Bool × α) (c : ι → Bool) (i : ι) : Bool := Bool.xor (x i).1 (c i)

def Compatible (x : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i j, (x i).2 = (x j).2 → required x c i = required x c j

def colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) : Bool :=
  Bool.xor (x i).1 (ξ (x i).2)

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma required_colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) :
    required x (colors x ξ) i = ξ (x i).2 := by
  simp only [required,colors]
  cases (x i).1 <;> cases ξ (x i).2 <;> rfl

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma colors_compatible (x : ι → Bool × α) (ξ : α → Bool) : Compatible x (colors x ξ) := by
  intro i j he
  simp only [required_colors,he]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma Compatible.tail_injective {x : ι ↪ Bool × α} {c : ι → Bool} (hc : Compatible x c) (b : Bool) :
    Function.Injective (fun i : {i : ι // c i = b} => (x i.val).2) := by
  intro i j he
  apply Subtype.ext
  apply x.injective
  apply Prod.ext
  · have hh := hc i j he
    simp only [required,i.property,j.property] at hh
    cases h₀ : (x i.val).1 <;> cases h₁ : (x j.val).1 <;> cases b <;> simp_all
  · exact he

def childEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    {i : ι // c i = b} ↪ α := ⟨fun i => (x i.val).2,hc.tail_injective b⟩

noncomputable def labelSet (e : ι ↪ Bool × α) : Finset (Bool × α) := Finset.univ.image e

def alternatingProjection (p : Bool → Equiv.Perm α) : Equiv.Perm α := (p false).symm * p true

noncomputable def alternatingCycles (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) : ℕ :=
  Fintype.card (RoutingNetwork.SelectedCycle
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e))

def switchedEmbedding (e : ι ↪ Bool × α) (ξ : α → Bool) : ι ↪ Bool × α :=
  e.trans (pairLayer ξ).toEmbedding

end Thorp.PairRouting

namespace Thorp

section
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

def sandwichShuffle {A B C D E F : Type*} :
    ((A × B) × C) × ((D × E) × F) ≃ ((A × D) × (B × E)) × (F × C) where
  toFun x := (((x.1.1.1,x.2.1.1),(x.1.1.2,x.2.1.2)),(x.2.2,x.1.2))
  invFun x := (((x.1.1.1,x.1.2.1),x.2.2),((x.1.1.2,x.1.2.2),x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def benesStepEquiv (d : ℕ) : BenesCoins (d+1) ≃
    (BenesCoins d × BenesCoins d) × ((Card d → Bool) × (Card d → Bool)) :=
  (Equiv.prodCongr (coinStepEquiv d) (coinStepEquiv d)).trans sandwichShuffle

noncomputable def palindromeCost : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2

end

noncomputable def palindromeLowCost (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if d+1 ≤ H then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc true) σ.1.2

end Thorp

namespace Thorp.HighHeight
open scoped BigOperators Classical

noncomputable def highCost (J d : ℕ) {ι : Type*} [Fintype ι]
    (x : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  palindromeCost d x ω-palindromeLowCost (J-1) d x ω

def MainStatement : Prop :=
  ∃ b δ C : ℝ, 0<b ∧ 0<δ ∧ 0<C ∧ ∃ J₀ : ℕ, 1≤J₀ ∧
    (∀ d k : ℕ, ∀ x : Fin k ↪ Card d, ∀ J : ℕ, J₀≤J →
      Real.log (finiteMean (fun ω : BenesCoins d => ((2:ℝ)^b)^(highCost J d x ω)))/Real.log 2 ≤
        C*k*(2:ℝ)^(-b*J)) ∧
    (∀ d k : ℕ, ∀ x : Fin k ↪ Card d,
      Real.log (finiteMean (fun ω : BenesCoins d => ((2:ℝ)^b)^(palindromeCost d x ω)))/Real.log 2 ≤
        C*k*((k:ℝ)/(2:ℝ)^d)^δ) ∧
    (∀ r s k : ℕ, ∀ x : Fin k ↪ Card (s+r), ∀ J : ℕ, J₀≤J → 2*s<J →
      ∀ (X : SwitchIndex (s+r) → Bool) (lo : Card r × SwitchIndex s → Bool),
      Real.log (finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
        ((2:ℝ)^b)^(highCost J (s+r) x (assembleBits r s lo hi,X))))/Real.log 2 ≤
          C*k*(2:ℝ)^(-b*J))

end Thorp.HighHeight

end ThorpNine.HighTail

end OAI
