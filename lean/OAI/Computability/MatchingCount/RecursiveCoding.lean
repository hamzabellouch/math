import OAI.Computability.MatchingCount.RawOddCut

namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode

def branchRepr {A B C : Type} : Branch A B C → Sum B (C×(A×A))
  | .leaf b => .inl b
  | .fork c x y => .inr (c,(x,y))
def commandRepr {A C : Type} : Command A C → Sum (ℕ×A) C
  | .call k a => .inl (k,a)
  | .join c => .inr c
instance {A B C : Type} [Coding A] [Coding B] [Coding C] : Coding (Branch A B C) := ⟨fun b => encode (branchRepr b)⟩
instance {A C : Type} [Coding A] [Coding C] : Coding (Command A C) := ⟨fun c => encode (commandRepr c)⟩
instance {A C : Type} [Inhabited A] : Inhabited (Command A C) := ⟨.call 0 default⟩

namespace Compile
open StackCode.Poly
variable {A B C D P : Type} [Coding A] [Coding B] [Coding C] [Coding D] [Coding P]
@[fun_prop] theorem leaf_poly : Poly (Branch.leaf : B → Branch A B C) :=
  (Poly.sumInl (β := C×(A×A))).reindex Branch.leaf id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem fork_poly : Poly (fun z : C×(A×A) => Branch.fork z.1 z.2.1 z.2.2 : C×(A×A) → Branch A B C) :=
  (Poly.sumInr (α := B)).reindex (fun z : C×(A×A) => Branch.fork z.1 z.2.1 z.2.2) id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem call_poly : Poly (fun z : ℕ×A => Command.call z.1 z.2 : ℕ×A → Command A C) :=
  (Poly.sumInl (β := C)).reindex (fun z : ℕ×A => Command.call z.1 z.2) id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem join_poly : Poly (Command.join : C → Command A C) :=
  (Poly.sumInr (α := ℕ×A)).reindex Command.join id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem branchCasesWith [Inhabited A] [Inhabited B] [Inhabited C]
    (p : P → Branch A B C) (f : P×B → D) (g : P×(C×(A×A)) → D)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | .leaf b => f (a,b) | .fork c x y => g (a,(c,(x,y)))) := by
  have hr : Poly (fun a => branchRepr (p a)) :=
    hp.reindex (fun a => branchRepr (p a)) id (fun _ => rfl) (fun _ => rfl)
  let repr : Sum B (C×(A×A)) → List B×List (C×(A×A)) :=
    fun x => match x with | .inl b => ([b],[]) | .inr c => ([],[c])
  have hc : Poly repr := Poly.identity.reindex repr repr (fun x => by cases x <;> rfl) (fun _ => rfl)
  have h : Poly (fun a => if (repr (branchRepr (p a))).1.isEmpty then
      g (a,(repr (branchRepr (p a))).2.headD default) else
      f (a,(repr (branchRepr (p a))).1.headD default)) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)

@[fun_prop] theorem commandCasesWith [Inhabited A] [Inhabited C]
    (p : P → Command A C) (f : P×(ℕ×A) → D) (g : P×C → D)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | .call k x => f (a,(k,x)) | .join c => g (a,c)) := by
  have hr : Poly (fun a => commandRepr (p a)) :=
    hp.reindex (fun a => commandRepr (p a)) id (fun _ => rfl) (fun _ => rfl)
  let repr : Sum (ℕ×A) C → List (ℕ×A)×List C :=
    fun x => match x with | .inl b => ([b],[]) | .inr c => ([],[c])
  have hc : Poly repr := Poly.identity.reindex repr repr (fun x => by cases x <;> rfl) (fun _ => rfl)
  have h : Poly (fun a => if (repr (commandRepr (p a))).1.isEmpty then
      g (a,(repr (commandRepr (p a))).2.headD default) else
      f (a,(repr (commandRepr (p a))).1.headD default)) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)
end Compile
end BinaryMatching.RecursiveEval
end

end OAI
