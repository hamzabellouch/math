import Mathlib
import OAI.Computability.SolenoidalRecorder.Machines

namespace OAI

/-! Full-domain reversible recorder instructions and unique predecessors. -/

namespace Solenoidal
namespace Recorder
variable (M : Machine)

 
inductive History
  | empty | frontier | record (r : M.Instruction)
  deriving DecidableEq, Fintype

inductive Control
  | S (q : M.State) | A (r : M.Instruction) | R (r : M.Instruction)
  | F (q : M.State) | L (q : M.State)
  deriving DecidableEq, Fintype

@[ext] structure Letter where
  work : M.Symbol
  history : History M
  mark : Bool
  deriving DecidableEq, Fintype

 

inductive Rule : Control M → Letter M → Control M → Letter M → Move → Prop
  | work (r : M.Instruction) (ℓ : History M) (hℓ : ℓ ≠ .frontier) :
      Rule (.S r.oldState) ⟨r.read, ℓ, false⟩ (.A r) ⟨r.write, ℓ, false⟩ r.move
  | mark (r : M.Instruction) (c : M.Symbol) (ℓ : History M) (hℓ : ℓ ≠ .frontier) :
      Rule (.A r) ⟨c, ℓ, false⟩ (.R r) ⟨c, ℓ, true⟩ .right
  | scanRight (r : M.Instruction) (c : M.Symbol) (ℓ : History M)
      (hℓ : ℓ ≠ .frontier) :
      Rule (.R r) ⟨c, ℓ, false⟩ (.R r) ⟨c, ℓ, false⟩ .right
  | record (r : M.Instruction) (c : M.Symbol) :
      Rule (.R r) ⟨c, .frontier, false⟩ (.F r.nextState) ⟨c, .record r, false⟩ .right
  | advance (q : M.State) (c : M.Symbol) :
      Rule (.F q) ⟨c, .empty, false⟩ (.L q) ⟨c, .frontier, false⟩ .left
  | scanLeft (q : M.State) (c : M.Symbol) (ℓ : History M) (hℓ : ℓ ≠ .frontier) :
      Rule (.L q) ⟨c, ℓ, false⟩ (.L q) ⟨c, ℓ, false⟩ .left
  | finish (q : M.State) (c : M.Symbol) (ℓ : History M) (hℓ : ℓ ≠ .frontier) :
      Rule (.L q) ⟨c, ℓ, true⟩ (.S q) ⟨c, ℓ, false⟩ .stay

 
def incoming : Control M → Move
  | .S _ => .stay
  | .A r => r.move
  | .R _ => .right
  | .F _ => .right
  | .L _ => .left

 

def undo (s : Control M) (b : Letter M) : Control M × Letter M :=
  match s with
  | .A r => (.S r.oldState, ⟨r.read, b.history, false⟩)
  | .R r => if b.mark then (.A r, ⟨b.work, b.history, false⟩) else (.R r, b)
  | .F q => match b.history with
      | .record r => (.R r, ⟨b.work, .frontier, false⟩)
      | _ => (.S q, b)
  | .L q => if b.history = .frontier then (.F q, ⟨b.work, .empty, false⟩)
      else (.L q, b)
  | .S q => (.L q, ⟨b.work, b.history, true⟩)

variable {M} {s s' s₁ s₂ : Control M} {a b a₁ a₂ : Letter M} {d d₁ d₂ : Move}

 
theorem fixed_incoming (h : Rule M s a s' b d) : d = incoming M s' := by
  cases h <;> rfl

 
theorem undo_rule (h : Rule M s a s' b d) : undo M s' b = (s, a) := by
  cases h <;> simp_all [undo]

 
theorem local_predecessor_unique
    (h₁ : Rule M s₁ a₁ s' b d₁) (h₂ : Rule M s₂ a₂ s' b d₂) :
    s₁ = s₂ ∧ a₁ = a₂ ∧ d₁ = d₂ := by
  have hu : (s₁, a₁) = (s₂, a₂) := (undo_rule h₁).symm.trans (undo_rule h₂)
  exact ⟨congrArg Prod.fst hu, congrArg Prod.snd hu,
    (fixed_incoming h₁).trans (fixed_incoming h₂).symm⟩

 
theorem rule_deterministic {u₁ u₂ t₁ t₂ : Control M} {a₁ a₂ b₁ b₂ : Letter M}
    (h₁ : Rule M u₁ a₁ t₁ b₁ d₁) (h₂ : Rule M u₂ a₂ t₂ b₂ d₂)
    (hu : u₁ = u₂) (ha : a₁ = a₂) :
    t₁ = t₂ ∧ b₁ = b₂ ∧ d₁ = d₂ := by
  cases h₁ <;> cases h₂ <;>
    simp_all [Letter.mk.injEq, Machine.Instruction.oldState, Machine.Instruction.read]
  rename_i r₁ ℓ₁ r₂ ℓ₂ hℓ
  have hr : r₁ = r₂ := Subtype.ext (Prod.ext hu ha.1)
  simp [hr]

@[ext] structure Config (M : Machine) where
  control : Control M
  head : ℤ
  tape : ℤ → Letter M

 
def successor (c : Config M) (s : Control M) (b : Letter M) (d : Move) : Config M :=
  ⟨s, c.head + d.displacement, Function.update c.tape c.head b⟩

def Step (c c' : Config M) : Prop :=
  ∃ s b d, Rule M c.control (c.tape c.head) s b d ∧ c' = successor c s b d

 
theorem step_deterministic {c c₁ c₂ : Config M}
    (h₁ : Step c c₁) (h₂ : Step c c₂) : c₁ = c₂ := by
  obtain ⟨s₁, b₁, d₁, hr₁, he₁⟩ := h₁
  obtain ⟨s₂, b₂, d₂, hr₂, he₂⟩ := h₂
  obtain ⟨rfl, rfl, rfl⟩ := rule_deterministic hr₁ hr₂ rfl rfl
  exact he₁.trans he₂.symm

 
theorem predecessor_unique {c₁ c₂ c' : Config M}
    (h₁ : Step c₁ c') (h₂ : Step c₂ c') : c₁ = c₂ := by
  obtain ⟨s₁, b₁, d₁, hr₁, he₁⟩ := h₁
  obtain ⟨s₂, b₂, d₂, hr₂, he₂⟩ := h₂
  have he : successor c₁ s₁ b₁ d₁ = successor c₂ s₂ b₂ d₂ := he₁.symm.trans he₂
  have hs : s₁ = s₂ := congrArg Config.control he
  subst s₂
  have hd : d₁ = d₂ := (fixed_incoming hr₁).trans (fixed_incoming hr₂).symm
  subst d₂
  have hh : c₁.head = c₂.head := add_right_cancel (congrArg Config.head he)
  have ht : Function.update c₁.tape c₁.head b₁ = Function.update c₂.tape c₂.head b₂ :=
    congrArg Config.tape he
  have hb : b₁ = b₂ := by
    have := congrFun ht c₁.head
    simpa [hh] using this
  subst b₂
  obtain ⟨hc, ha, _⟩ := local_predecessor_unique hr₁ hr₂
  apply Config.ext hc hh
  funext k
  by_cases hk : k = c₁.head
  · subst k
    simpa only [hh] using ha
  · have hk' : k ≠ c₂.head := by simpa only [hh] using hk
    simpa [Function.update_of_ne hk, Function.update_of_ne hk'] using congrFun ht k
end Recorder
end Solenoidal

end OAI
