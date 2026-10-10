import OAI.Computability.Superstring.Iteration

namespace OAI

namespace Superstring.BitCode

namespace Steps

 theorem terminal_unique {K L : Type} [DecidableEq K] {code : L → Instr K (Option L)}
    {c : Option L × Store K} {n m : ℕ} {s t : Store K}
    (h : Steps code c n (none, s)) (g : Steps code c m (none, t)) : s = t := by
  induction n generalizing c m s t with
  | zero => cases h; cases g; rfl
  | succ n ih =>
    cases h with
    | step l u h =>
      cases g with
      | step _ _ g => exact ih h g

end Steps

namespace Block

 theorem Exec.deterministic {K : Type} [DecidableEq K] {b : Block K}
    {r s t : Store K} {n m : ℕ} (h : b.Exec r s n) (g : b.Exec r t m) : s = t :=
  Steps.terminal_unique (exec_steps h) (exec_steps g)

end Block

 theorem Parses.separate {α : Type} {e : α → List Bool} (hp : Parses e)
    {a b : α} {x y : List Bool} (he : e a ++ x = e b ++ y) :
    e a = e b ∧ x = y := by
  obtain ⟨K, inst, code, c, hc⟩ := hp
  obtain ⟨n, _, ha⟩ := hc a x []
  obtain ⟨m, _, hb⟩ := hc b y []
  rw [he] at ha
  have hh := ha.deterministic hb
  have hx := congrFun hh inputPort
  have ho := congrFun hh outputPort
  change x = y at hx
  change (e a).reverse ++ [] = (e b).reverse ++ [] at ho
  simp only [List.append_nil] at ho
  exact ⟨List.reverse_injective ho, hx⟩


class Coded (α : Type) where
  code : α → List Bool
  parses : Parses code
  injective : Function.Injective code

abbrev bits {α : Type} [Coded α] : α → List Bool := Coded.code
abbrev bitSize {α : Type} [Coded α] (a : α) := (bits a).length

def Poly {α β : Type} [Coded α] [Coded β] (f : α → β) : Prop :=
  RunsInPolyTime bits bits f

instance codedBool : Coded Bool where
  code b := [b]
  parses := Parses.bit
  injective := by intro a b h; exact List.singleton_injective h

instance codedUnit : Coded Unit where
  code _ := []
  parses := Parses.const []
  injective := fun _ _ _ => Subsingleton.elim _ _

instance codedNat : Coded ℕ where
  code := natCode
  parses := Parses.nat
  injective := by
    intro a b h
    have hh := congrArg List.length h
    simp only [length_natCode] at hh
    omega

instance codedProd {α β : Type} [Coded α] [Coded β] : Coded (α × β) where
  code p := bits p.1 ++ bits p.2
  parses := Coded.parses.prod Coded.parses
  injective := by
    intro a b h
    obtain ⟨hh, ht⟩ := Coded.parses.separate h
    exact Prod.ext (Coded.injective hh) (Coded.injective ht)

instance codedList {α : Type} [Coded α] : Coded (List α) where
  code := listCode bits
  parses := Coded.parses.list
  injective := by
    intro a b h
    induction a generalizing b with
    | nil => cases b with
      | nil => rfl
      | cons b bs => simp only [listCode, List.cons.injEq, Bool.true_eq_false, false_and] at h
    | cons a as ih => cases b with
      | nil => simp only [listCode, List.cons.injEq, Bool.false_eq_true, false_and] at h
      | cons b bs =>
        have he : bits a ++ listCode bits as = bits b ++ listCode bits bs := List.cons.inj h |>.2
        obtain ⟨ha, ht⟩ := Coded.parses.separate he
        exact congrArg₂ List.cons (Coded.injective ha) (ih ht)

@[simp] theorem bits_bool (b : Bool) : bits b = [b] := rfl
@[simp] theorem bits_unit (u : Unit) : bits u = [] := rfl
@[simp] theorem bits_nat (n : ℕ) : bits n = natCode n := rfl
@[simp] theorem bits_prod {α β : Type} [Coded α] [Coded β] (a : α) (b : β) :
    bits (a, b) = bits a ++ bits b := rfl
@[simp] theorem bits_nil {α : Type} [Coded α] : bits ([] : List α) = [true] := rfl
@[simp] theorem bits_cons {α : Type} [Coded α] (a : α) (as : List α) :
    bits (a :: as) = false :: (bits a ++ bits as) := rfl
@[simp] theorem bitSize_nat (n : ℕ) : bitSize n = n + 1 := length_natCode n
@[simp] theorem bitSize_prod {α β : Type} [Coded α] [Coded β] (a : α) (b : β) :
    bitSize (a, b) = bitSize a + bitSize b := List.length_append
@[simp] theorem bitSize_nil {α : Type} [Coded α] : bitSize ([] : List α) = 1 := rfl
@[simp] theorem bitSize_cons {α : Type} [Coded α] (a : α) (as : List α) :
    bitSize (a :: as) = 1 + bitSize a + bitSize as := by
  simp only [bitSize, bits_cons, List.length_cons, List.length_append]; omega

 theorem length_le_bitSize {α : Type} [Coded α] (as : List α) : as.length + 1 ≤ bitSize as := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [bitSize_cons, List.length_cons]; omega

namespace Poly

variable {α β γ δ : Type} [Coded α] [Coded β] [Coded γ] [Coded δ]

 theorem id : Poly (_root_.id : α → α) := RunsInPolyTime.id bits
 theorem const (b : β) : Poly (fun _ : α => b) := RunsInPolyTime.const bits bits b
 theorem comp {f : α → β} {g : β → γ} (hg : Poly g) (hf : Poly f) : Poly (g ∘ f) :=
   RunsInPolyTime.comp hg hf
 theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) :
     Poly (fun a => (f a, g a)) := RunsInPolyTime.pair hf hg
 theorem fst : Poly (Prod.fst : α × β → α) := RunsInPolyTime.fst bits Coded.parses
 theorem snd : Poly (Prod.snd : α × β → β) := RunsInPolyTime.snd bits Coded.parses
 theorem cons : Poly (fun p : α × List α => p.1 :: p.2) := RunsInPolyTime.cons bits
 theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
     Poly (fun a => if p a then f a else g a) := by
   have hb := RunsInPolyTime.boolCase hf hg
   have hp' := hp.pair (id : Poly (_root_.id : α → α))
   exact hb.comp hp'
 theorem iterate {f : α → α} (hf : Poly f) (R : Polynomial ℕ)
     (hs : ∀ n a j, j < n → bitSize (f^[j] a) ≤ R.eval (bitSize (n, a))) :
     Poly (fun p : ℕ × α => f^[p.1] p.2) := RunsInPolyTime.iterate hf R hs

 theorem output_size {f : α → β} (hf : Poly f) :
     ∃ P : Polynomial ℕ, ∀ a, bitSize (f a) ≤ P.eval (bitSize a) :=
   RunsInPolyTime.output_length hf

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 def sumCode {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : α ⊕ β → List Bool
   | .inl a => false :: ea a
   | .inr b => true :: eb b

 theorem Parses.sum {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Parses ea) (hz : Parses eb) : Parses (sumCode ea eb) := by
  obtain ⟨K, instK, b, c, hb⟩ := ha
  obtain ⟨L, instL, d, e, hd⟩ := hz
  let left : Block (Ports (K ⊕ L)) := b.rename (Sum.map _root_.id Sum.inl)
  let right : Block (Ports (K ⊕ L)) := d.rename (Sum.map _root_.id Sum.inr)
  let code : Block (Ports (K ⊕ L)) := .branch inputPort .skip
    (.seq (Block.readBit inputPort outputPort) left)
    (.seq (Block.readBit inputPort outputPort) right)
  refine ⟨K ⊕ L, inferInstance, code, c + e + 4, ?_⟩
  intro a tail acc
  cases a with
  | inl a =>
    obtain ⟨n, hn, hh⟩ := hb a tail (false :: acc)
    have hrun := hh.ports (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
    have hread := Block.readBit_exec false (ea a ++ tail) acc (fun _ : K ⊕ L => [])
    have he := Block.Exec.branch_false (k := (inputPort : Ports (K ⊕ L))) (a := Block.skip)
      (c := .seq (Block.readBit inputPort outputPort) right) rfl (Block.Exec.seq hread hrun)
    refine ⟨3 + n + 1, ?_, ?_⟩
    · simp only [sumCode, List.length_cons]; nlinarith
    · simpa only [sumCode, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, pairStore] using he
  | inr a =>
    obtain ⟨n, hn, hh⟩ := hd a tail (true :: acc)
    have hrun := hh.ports (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
    have hread := Block.readBit_exec true (eb a ++ tail) acc (fun _ : K ⊕ L => [])
    have he := Block.Exec.branch_true (k := (inputPort : Ports (K ⊕ L))) (a := Block.skip)
      (b := .seq (Block.readBit inputPort outputPort) left) rfl (Block.Exec.seq hread hrun)
    refine ⟨3 + n + 1, ?_, ?_⟩
    · simp only [sumCode, List.length_cons]; nlinarith
    · simpa only [sumCode, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, pairStore] using he

instance codedSum {α β : Type} [Coded α] [Coded β] : Coded (α ⊕ β) where
  code := sumCode bits bits
  parses := Coded.parses.sum Coded.parses
  injective := by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Coded.injective (List.cons.inj h).2)
      | inr b => simp only [sumCode, List.cons.injEq, Bool.false_eq_true, false_and] at h
    | inr a => cases b with
      | inl b => simp only [sumCode, List.cons.injEq, Bool.true_eq_false, false_and] at h
      | inr b => exact congrArg Sum.inr (Coded.injective (List.cons.inj h).2)

@[simp] theorem bits_inl {α β : Type} [Coded α] [Coded β] (a : α) :
    bits (Sum.inl a : α ⊕ β) = false :: bits a := rfl
@[simp] theorem bits_inr {α β : Type} [Coded α] [Coded β] (b : β) :
    bits (Sum.inr b : α ⊕ β) = true :: bits b := rfl

namespace Poly

 theorem sumCases {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : α → γ} {g : β → γ} (hf : Poly f) (hg : Poly g) : Poly (Sum.elim f g) := by
  obtain ⟨K, instK, b, P, hb⟩ := hf.canonical
  obtain ⟨L, instL, c, Q, hc⟩ := hg.canonical
  let bf : Block (Workspace (K ⊕ L)) := b.rename (Sum.map _root_.id Sum.inl)
  let bt : Block (Workspace (K ⊕ L)) := c.rename (Sum.map _root_.id Sum.inr)
  let code : Block (Workspace (K ⊕ L)) := .branch workPort .skip
    (.seq (.pop workPort) bf) (.seq (.pop workPort) bt)
  refine ⟨Workspace (K ⊕ L), inferInstance, workPort, workPort, code, P + Q + 2, ?_⟩
  intro a
  have hpop (v : Bool) (w : List Bool) : Block.Exec (.pop workPort)
      (workStore (v :: w) (fun _ : K ⊕ L => []))
      (workStore w (fun _ : K ⊕ L => [])) 1 := by
    have he : Function.update (fun _ : Unit => v :: w) () w =
        fun _ : Unit => w := by funext k; cases k; simp
    simpa only [workStore, workPort, Sum.elim_inl, List.tail_cons,
      Block.update_left, he] using
      Block.Exec.pop (workPort : Workspace (K ⊕ L))
        (workStore (v :: w) (fun _ : K ⊕ L => []))
  cases a with
  | inl a =>
    obtain ⟨n, hn, hh⟩ := hb a
    have hrun := hh.workspace (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_false (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (c := .seq (.pop workPort) bt) rfl (Block.Exec.seq (hpop false (bits a)) hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hp : P.eval (bits a).length ≤ P.eval (false :: bits a).length := eval_mono_nat P (by simp)
      simp only [bits_inl, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, bits_inl, Sum.elim_inl] using he
  | inr a =>
    obtain ⟨n, hn, hh⟩ := hc a
    have hrun := hh.workspace (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_true (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (b := .seq (.pop workPort) bf) rfl (Block.Exec.seq (hpop true (bits a)) hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hq : Q.eval (bits a).length ≤ Q.eval (true :: bits a).length := eval_mono_nat Q (by simp)
      simp only [bits_inr, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, bits_inr, Sum.elim_inr] using he

/-- Merely changing a typed view of the SAME input bits does not execute the
view function. This is used only with an explicit encoding equality below. -/
 theorem reencode {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : β → γ} (hf : Poly f) (r : α → β) (he : ∀ a, bits (r a) = bits a) :
    Poly (f ∘ r) := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := hf
  refine ⟨K, inst, i, o, b, P, ?_⟩
  intro a
  simpa only [he, Function.comp_apply] using hb (r a)

/-- One-step list destructor, implemented only by the leading spine marker.
The nonempty branch receives exactly the head followed by the encoded tail. -/
 theorem listCases {α β : Type} [Coded α] [Coded β] (z : β)
    {f : α × List α → β} (hf : Poly f) :
    Poly (fun xs : List α => match xs with | [] => z | x :: xs => f (x, xs)) := by
  let view : List α → (α × List α) ⊕ Unit
    | [] => .inr ()
    | x :: xs => .inl (x, xs)
  have he (xs : List α) : bits (view xs) = bits xs := by cases xs <;> rfl
  convert (hf.sumCases (const z : Poly (fun _ : Unit => z))).reencode view he using 1
  funext xs; cases xs <;> rfl

 theorem tail {α : Type} [Coded α] : Poly (List.tail : List α → List α) :=
   listCases [] snd

 theorem headD {α : Type} [Coded α] (z : α) : Poly (fun xs : List α => xs.headD z) := by
   convert listCases z (fst : Poly (Prod.fst : α × List α → α)) using 1
   funext xs; cases xs <;> rfl

 theorem isEmpty {α : Type} [Coded α] : Poly (List.isEmpty : List α → Bool) :=
   listCases true (const false)

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

namespace Block

 def countBits {K : Type} (i o : K) : Block K := .loop i (.seq (.pop i) (.push o false))

 theorem countBits_exec {K : Type} [DecidableEq K] (w : List Bool) (j : ℕ) (z : Store K) :
    (countBits inputPort outputPort).Exec (portStore w (natCode j) z)
      (portStore [] (natCode (w.length + j)) z) (3 * w.length + 1) := by
  induction w generalizing j with
  | nil => simpa [countBits] using (Exec.loop_nil (a := .seq (.pop inputPort) (.push outputPort false)) (rfl : portStore [] (natCode j) z inputPort = []))
  | cons b w ih =>
    have hp : Exec (.pop inputPort) (portStore (b :: w) (natCode j) z)
        (portStore w (natCode j) z) 1 := by
      simpa only [portStore_input, List.tail_cons, update_input] using
        Exec.pop inputPort (portStore (b :: w) (natCode j) z)
    have hq : Exec (.push outputPort false) (portStore w (natCode j) z)
        (portStore w (natCode (j + 1)) z) 1 := by
      simpa only [portStore_output, update_output, natCode] using
        Exec.push outputPort false (portStore w (natCode j) z)
    have he := Exec.loop_cons (show portStore (b :: w) (natCode j) z inputPort ≠ [] from List.cons_ne_nil _ _) (Exec.seq hp hq) (ih (j + 1))
    simpa only [countBits, List.length_cons,
      show w.length + 1 + j = w.length + (j + 1) by omega,
      show 3 * (w.length + 1) + 1 = 1 + 1 + (3 * w.length + 1) + 1 by omega] using he

end Block

namespace Poly

 theorem size {α : Type} [Coded α] : Poly (bitSize : α → ℕ) := by
  let code : Block (Ports Unit) := .seq (.push outputPort true)
    (Block.countBits inputPort outputPort)
  refine ⟨Ports Unit, inferInstance, inputPort, outputPort, code, 3 * Polynomial.X + 2, ?_⟩
  intro a
  have hp : Block.Exec (.push outputPort true) (pairStore (bits a) [] : Store (Ports Unit))
      (pairStore (bits a) (natCode 0)) 1 := by
    simpa only [pairStore, portStore_output, update_output, natCode] using
      Block.Exec.push (outputPort : Ports Unit) true (pairStore (bits a) [])
  have he := Block.Exec.seq hp (Block.countBits_exec (bits a) 0 (fun _ : Unit => []))
  refine ⟨1 + (3 * (bits a).length + 1), ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]; omega
  · have he' : code.Exec (pairStore (bits a) [])
        (pairStore [] (natCode (bits a).length)) (1 + (3 * (bits a).length + 1)) := by
      simpa only [code, pairStore, Nat.add_zero] using he
    change code.Exec (single inputPort (bits a)) (single outputPort (natCode (bits a).length)) _
    simpa only [pairStore_input, pairStore_output] using he'

 theorem succ : Poly (Nat.succ : ℕ → ℕ) := by
  refine ⟨Unit, inferInstance, (), (), .push () false, 1, ?_⟩
  intro a
  refine ⟨1, by simp, ?_⟩
  have he : Function.update (single () (bits a)) () (false :: single () (bits a) ()) =
      single () (bits a.succ) := by funext k; cases k; simp [single, natCode]
  simpa only [he] using Block.Exec.push () false (single () (bits a))

 theorem listCasesWith {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {z : β → γ} {f : α × (List α × β) → γ} (hz : Poly z) (hf : Poly f) :
    Poly (fun p : List α × β => match p.1 with
      | [] => z p.2 | x :: xs => f (x, xs, p.2)) := by
  let view : List α × β → (α × (List α × β)) ⊕ β
    | ([], b) => .inr b
    | (x :: xs, b) => .inl (x, xs, b)
  have he (p : List α × β) : bits (view p) = bits p := by
    rcases p with ⟨xs, b⟩; cases xs <;>
      simp only [view, bits_inl, bits_inr, bits_prod, bits_nil, bits_cons,
        List.nil_append, List.cons_append, List.append_assoc]
  convert (hf.sumCases hz).reencode view he using 1
  funext p; rcases p with ⟨xs, b⟩; cases xs <;> rfl

 theorem natCasesWith {β γ : Type} [Coded β] [Coded γ]
    {z : β → γ} {f : ℕ × β → γ} (hz : Poly z) (hf : Poly f) :
    Poly (fun p : ℕ × β => match p.1 with
      | 0 => z p.2 | n + 1 => f (n, p.2)) := by
  let view : ℕ × β → (ℕ × β) ⊕ β
    | (0, b) => .inr b
    | (n + 1, b) => .inl (n, b)
  have he (p : ℕ × β) : bits (view p) = bits p := by
    rcases p with ⟨n, b⟩; cases n <;>
      simp only [view, bits_inl, bits_inr, bits_prod, bits_nat, natCode,
        List.nil_append, List.cons_append]
  convert (hf.sumCases hz).reencode view he using 1
  funext p; rcases p with ⟨n, b⟩; cases n <;> rfl

end Poly

end Superstring.BitCode

end OAI
