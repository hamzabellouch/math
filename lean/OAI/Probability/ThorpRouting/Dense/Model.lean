import Mathlib

namespace OAI

namespace ThorpNine.Dense

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

end Thorp

namespace Thorp.DenseTruncation
open scoped BigOperators

def AdmissibleCycleLaw (j : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ l, 0 ≤ p l) ∧ HasSum p 1 ∧
    ∀ l, p l ≤ ((l + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j - 1)

noncomputable def h (j : ℕ) : ℝ :=
  sSup {z : ℝ | ∃ p : ℕ → ℝ, AdmissibleCycleLaw j p ∧
    z = ∑' l : ℕ, p l / ((l + 1 : ℕ) : ℝ)}

def AdmissibleAllocation (ρ : ℝ) (x : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
    (∑' j : ℕ, x j / (2 : ℝ) ^ (j + 1)) ≤ ρ

noncomputable def H (ρ : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ x : ℕ → ℝ, AdmissibleAllocation ρ x ∧
    z = (1 / 2 : ℝ) * ∑' j : ℕ, h (j + 1) * x j}

noncomputable def entropyCorrection (ρ : ℝ) : ℝ :=
  (-ρ - (1 - ρ) * Real.log (1 - ρ)) / (ρ * Real.log 2)

noncomputable def densityExponent (d r : ℕ) (x : Fin r ↪ Card d)
    (ω : BenesCoins d) : ℝ :=
  palindromeCost d x ω +
    Real.log (((2 ^ d).descFactorial r : ℝ) / ((2 : ℝ) ^ d) ^ r) / Real.log 2

def MainStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∀ d r : ℕ, 1 ≤ d → 1 ≤ r →
      (r : ℝ) / (2 : ℝ) ^ d = ρ → ∀ x : Fin r ↪ Card d,
      finiteMean (fun ω : BenesCoins d =>
        if (r : ℝ) * (H ρ + entropyCorrection ρ + ε) < densityExponent d r x ω
        then (1 : ℝ) else 0) ≤ Real.exp (-c * r)

end Thorp.DenseTruncation

end ThorpNine.Dense

end OAI
