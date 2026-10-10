import OAI.Computability.DegreeRigidity.OrdinalCodes.OmegaModelCoreClosure

namespace OAI

namespace TuringRigidity.OmegaModelCore.OmegaData
open BoundedSetTheory
universe u
noncomputable section
variable {α : Type u} (S : OmegaData α)

def push {β : Type*} (x : β) (e : ℕ → β) : ℕ → β
  | 0 => x
  | n+1 => e n

def Eval (e : ℕ → α) : Formula → Prop
  | .equal i j => e i = e j
  | .member i j => S.mem (e i) (e j)
  | .conj p q => Eval e p ∧ Eval e q
  | .neg p => ¬ Eval e p
  | .existsMem i p => ∃ x, S.mem x (e i) ∧ Eval (push x e) p

theorem collapse_eval (p : Formula) (e : ℕ → S.Core) :
    p.Eval (fun i => S.collapse (e i)) ↔ S.Eval (fun i => (e i).val) p := by
  induction p generalizing e with
  | equal i j =>
    change S.collapse (e i) = S.collapse (e j) ↔ (e i).val = (e j).val
    exact ⟨fun h => congrArg Subtype.val (S.collapse_injective h),
      fun h => congrArg S.collapse (Subtype.ext h)⟩
  | member i j => exact S.collapse_mem_iff (e i) (e j)
  | conj p q hp hq => exact and_congr (hp e) (hq e)
  | neg p hp => exact not_congr (hp e)
  | existsMem i p hp =>
    have hstep (y : S.Core) : p.Eval (cons (S.collapse y) (fun i => S.collapse (e i))) ↔
        S.Eval (push y.val (fun i => (e i).val)) p := by
      have he : (fun i => S.collapse (push y e i)) =
          cons (S.collapse y) (fun i => S.collapse (e i)) := by
        funext i
        cases i <;> rfl
      have hv : (fun i => (push y e i).val) = push y.val (fun i => (e i).val) := by
        funext i
        cases i <;> rfl
      simpa only [he,hv] using hp (push y e)
    constructor
    · rintro ⟨x,hx,hp'⟩
      obtain ⟨y,hy,rfl⟩ := (S.mem_collapse (e i) x).mp hx
      exact ⟨y.val,hy,(hstep y).mp hp'⟩
    · rintro ⟨x,hx,hp'⟩
      let y : S.Core := ⟨x,S.core_transitive (e i).property hx⟩
      exact ⟨S.collapse y,(S.mem_collapse (e i) _).mpr ⟨y,hx,rfl⟩,
        (hstep y).mpr hp'⟩

def PairingAxiom : Prop := ∀ a b : α, ∃ c, ∀ x, S.mem x c ↔ x=a ∨ x=b

def UnionAxiom : Prop := ∀ a : α, ∃ b, ∀ x, S.mem x b ↔ ∃ y, S.mem y a ∧ S.mem x y

def SeparationAxiom : Prop := ∀ (p : Formula) (e : ℕ → α) (a : α),
  ∃ b, ∀ x, S.mem x b ↔ S.mem x a ∧ S.Eval (push x e) p

end
end TuringRigidity.OmegaModelCore.OmegaData

end OAI
