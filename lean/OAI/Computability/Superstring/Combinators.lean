import OAI.Computability.Superstring.Encoding

namespace OAI

namespace Superstring.BitCode

 theorem bitSize_sublist {α : Type} [Coded α] {xs ys : List α} (h : xs.Sublist ys) :
    bitSize xs ≤ bitSize ys := by
  induction h with
  | slnil => exact le_rfl
  | cons b h ih => simp only [bitSize_cons]; omega
  | cons_cons b h ih => simp only [bitSize_cons]; omega

 theorem bitSize_append {α : Type} [Coded α] (xs ys : List α) :
    bitSize (xs ++ ys) + 1 = bitSize xs + bitSize ys := by
  induction xs with
  | nil => simp [Nat.add_comm]
  | cons x xs ih => simp only [List.cons_append, bitSize_cons]; omega

 def foldStep {α β : Type} (f : β → α → β) (p : List α × β) : List α × β :=
   match p.1 with
   | [] => p
   | x :: xs => (xs, f p.2 x)

 theorem iterate_foldStep {α β : Type} (f : β → α → β) (n : ℕ) (xs : List α) (a : β) :
    (foldStep f)^[n] (xs, a) = (xs.drop n, (xs.take n).foldl f a) := by
  induction n generalizing xs a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simpa only [foldStep, List.take_nil, List.drop_nil, List.foldl_nil] using ih [] a
    | cons x xs => simpa only [foldStep, List.take_succ_cons, List.drop_succ_cons,
        List.foldl_cons] using ih xs (f a x)

namespace Poly

 theorem foldStep {α β : Type} [Coded α] [Coded β] {f : β → α → β}
    (hf : Poly (fun p : β × α => f p.1 p.2)) : Poly (foldStep f) := by
  have hn : Poly (fun a : β => (([] : List α), a)) := (const []).pair id
  have hc : Poly (fun p : α × (List α × β) => (p.2.1, f p.2.2 p.1)) :=
    (fst.comp snd).pair (hf.comp ((snd.comp snd).pair fst))
  convert listCasesWith hn hc using 1
  funext p; rcases p with ⟨xs, a⟩; cases xs <;> rfl

/-- A bounded list fold, with its genuine encoded-data invariant exposed.
The bound concerns mathematical intermediate values, not an assumed runtime. -/
 theorem foldl {α β : Type} [Coded α] [Coded β] {f : β → α → β}
    (hf : Poly (fun p : β × α => f p.1 p.2)) (R : Polynomial ℕ)
    (hs : ∀ (xs : List α) (a : β) (j : ℕ), bitSize ((xs.take j).foldl f a) ≤ R.eval (bitSize (xs, a))) :
    Poly (fun p : List α × β => p.1.foldl f p.2) := by
  have hi : Poly (fun p : ℕ × (List α × β) => (Superstring.BitCode.foldStep f)^[p.1] p.2) := by
    apply (foldStep hf).iterate (Polynomial.X + R)
    intro n p j _
    rcases p with ⟨xs, a⟩
    rw [iterate_foldStep]
    simp only [bitSize_prod, Polynomial.eval_add, Polynomial.eval_X]
    have hd := bitSize_sublist (List.drop_sublist j xs)
    have hb := hs xs a j
    have hr := eval_mono_nat R (show bitSize (xs, a) ≤ bitSize n + (bitSize xs + bitSize a) by simp)
    simp only [bitSize_prod] at hb hr
    omega
  have htimer : Poly (fun p : List α × β => (bitSize p.1, p)) :=
    (size.comp fst).pair id
  have he : (fun p : List α × β => ((Superstring.BitCode.foldStep f)^[bitSize p.1] p).2) =
      fun p => p.1.foldl f p.2 := by
    funext p
    rcases p with ⟨xs, a⟩
    rw [iterate_foldStep]
    simp only [List.take_of_length_le (show xs.length ≤ bitSize xs by have := length_le_bitSize xs; omega)]
  exact he ▸ snd.comp (hi.comp htimer)

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 theorem bitSize_mem {α : Type} [Coded α] {x : α} {xs : List α} (h : x ∈ xs) :
    bitSize x ≤ bitSize xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [bitSize_cons]; omega
    · have := ih h; simp only [bitSize_cons]; omega

 theorem foldl_size_additive {α β : Type} [Coded α] [Coded β]
    (f : β → α → β) (Q : Polynomial ℕ)
    (hf : ∀ a x, bitSize (f a x) ≤ bitSize a + Q.eval (bitSize x))
    (xs : List α) (M : ℕ) (hx : ∀ x ∈ xs, bitSize x ≤ M) (a : β) :
    bitSize (xs.foldl f a) ≤ bitSize a + xs.length * Q.eval M := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have hh := ih (fun y hy => hx y (List.mem_cons_of_mem x hy)) (f a x)
    have hg := hf a x
    have hm := eval_mono_nat Q (hx x (List.mem_cons_self))
    simp only [List.foldl_cons, List.length_cons]
    nlinarith

namespace Poly

 theorem foldl_additive {α β : Type} [Coded α] [Coded β] {f : β → α → β}
    (hf : Poly (fun p : β × α => f p.1 p.2)) (Q : Polynomial ℕ)
    (hs : ∀ a x, bitSize (f a x) ≤ bitSize a + Q.eval (bitSize x)) :
    Poly (fun p : List α × β => p.1.foldl f p.2) := by
  apply foldl hf (Polynomial.X + Polynomial.X * Q)
  intro xs a j
  let N := bitSize (xs, a)
  have hx : ∀ x ∈ xs.take j, bitSize x ≤ N := by
    intro x hx
    have hm := bitSize_mem (List.mem_of_mem_take hx)
    dsimp [N]; simp only [bitSize_prod]; omega
  have hb := foldl_size_additive f Q hs (xs.take j) N hx a
  have hl : (xs.take j).length ≤ N := by
    have h₁ : (xs.take j).length ≤ xs.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    have h₂ := length_le_bitSize xs
    dsimp [N]; simp only [bitSize_prod]; omega
  have ha : bitSize a ≤ N := by simp [N]
  have hmul := Nat.mul_le_mul_right (Q.eval N) hl
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  change bitSize ((xs.take j).foldl f a) ≤ N + N * Q.eval N
  omega

 theorem reverse {α : Type} [Coded α] : Poly (List.reverse : List α → List α) := by
  have hf : Poly (fun p : List α × α => p.2 :: p.1) := cons.comp (snd.pair fst)
  have hs : ∀ (a : List α) (x : α), bitSize (x :: a) ≤
      bitSize a + (Polynomial.X + 1 : Polynomial ℕ).eval (bitSize x) := by
    intros; simp only [bitSize_cons, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]; omega
  have hp := (foldl_additive hf (Polynomial.X + 1) hs).comp
    ((id : Poly (_root_.id : List α → List α)).pair (const ([] : List α)))
  convert hp using 1
  funext xs
  simp only [Function.comp_apply, _root_.id, List.foldl_flip_cons_eq_append', List.append_nil]

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

@[simp] theorem bitSize_reverse {α : Type} [Coded α] (xs : List α) :
    bitSize xs.reverse = bitSize xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h := bitSize_append xs.reverse [x]
    simp only [List.reverse_cons, bitSize_cons, bitSize_nil] at *
    omega

namespace Poly

 theorem map {α β : Type} [Coded α] [Coded β] {f : α → β}
    (hf : Poly f) : Poly (List.map f) := by
  obtain ⟨P, hP⟩ := hf.output_size
  have hstep : Poly (fun p : List β × α => f p.2 :: p.1) := cons.comp ((hf.comp snd).pair fst)
  have hs : ∀ (a : List β) (x : α), bitSize (f x :: a) ≤
      bitSize a + (P + 1).eval (bitSize x) := by
    intro a x
    have := hP x
    simp only [bitSize_cons, Polynomial.eval_add, Polynomial.eval_one]; omega
  have hp := reverse.comp ((foldl_additive hstep (P + 1) hs).comp
    ((id : Poly (_root_.id : List α → List α)).pair (const ([] : List β))))
  convert hp using 1
  funext xs
  simp only [Function.comp_apply, _root_.id, List.foldl_flip_cons_eq_append,
    List.append_nil, List.reverse_reverse]

 theorem append {α : Type} [Coded α] : Poly (fun p : List α × List α => p.1 ++ p.2) := by
  have hstep : Poly (fun p : List α × α => p.2 :: p.1) := cons.comp (snd.pair fst)
  have hs : ∀ (a : List α) (x : α), bitSize (x :: a) ≤
      bitSize a + (Polynomial.X + 1 : Polynomial ℕ).eval (bitSize x) := by
    intros; simp only [bitSize_cons, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]; omega
  have hp := (foldl_additive hstep (Polynomial.X + 1) hs).comp
    ((reverse.comp fst).pair (snd : Poly (Prod.snd : List α × List α → List α)))
  convert hp using 1
  funext p
  simp only [Function.comp_apply, List.foldl_flip_cons_eq_append', List.reverse_reverse]

 theorem length {α : Type} [Coded α] : Poly (List.length : List α → ℕ) := by
  have hf : Poly (fun p : ℕ × α => p.1 + 1) := succ.comp fst
  have hs : ∀ (a : ℕ) (x : α), bitSize (a + 1) ≤
      bitSize a + (1 : Polynomial ℕ).eval (bitSize x) := by intros; simp
  have hp := (foldl_additive hf 1 hs).comp
    ((id : Poly (_root_.id : List α → List α)).pair (const 0))
  convert hp using 1
  funext xs
  have hl (xs : List α) (n : ℕ) : xs.foldl (fun n _ => n + 1) n = n + xs.length := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih => simp only [List.foldl_cons, List.length_cons, ih]; omega
  simp only [Function.comp_apply, _root_.id, hl, Nat.zero_add]

 theorem not : Poly (Bool.not : Bool → Bool) := by
   convert ite (id : Poly (_root_.id : Bool → Bool)) (const false) (const true) using 1
   funext b; cases b <;> rfl

 theorem and : Poly (fun p : Bool × Bool => p.1 && p.2) := by
   convert ite (fst : Poly (Prod.fst : Bool × Bool → Bool)) snd (const false) using 1
   funext p; cases p with | mk b c => cases b <;> rfl

 theorem or : Poly (fun p : Bool × Bool => p.1 || p.2) := by
   convert ite (fst : Poly (Prod.fst : Bool × Bool → Bool)) (const true) snd using 1
   funext p; cases p with | mk b c => cases b <;> rfl

 theorem eqBool : Poly (fun p : Bool × Bool => decide (p.1 = p.2)) := by
   convert ite (fst : Poly (Prod.fst : Bool × Bool → Bool)) snd (not.comp snd) using 1
   funext p; cases p with | mk b c => cases b <;> cases c <;> rfl

 theorem pred : Poly (Nat.pred : ℕ → ℕ) := by
   have hp := (natCasesWith (const 0 : Poly (fun _ : Unit => 0))
      (fst : Poly (Prod.fst : ℕ × Unit → ℕ))).comp
      ((id : Poly (_root_.id : ℕ → ℕ)).pair (const ()))
   convert hp using 1
   funext n; cases n <;> rfl

 theorem isZero : Poly (fun n : ℕ => decide (n = 0)) := by
   have hp := (natCasesWith (const true : Poly (fun _ : Unit => true))
      (const false : Poly (fun _ : ℕ × Unit => false))).comp
      ((id : Poly (_root_.id : ℕ → ℕ)).pair (const ()))
   convert hp using 1
   funext n; cases n <;> rfl

 theorem add : Poly (fun p : ℕ × ℕ => p.1 + p.2) := by
   have hi := succ.iterate (2 * Polynomial.X)
     (by intro n a j hj
         have he : Nat.succ^[j] a = a + j := by
           induction j with
           | zero => simp
           | succ j ih => simp only [Function.iterate_succ_apply']; omega
         simp only [he, bitSize_nat, bitSize_prod, Polynomial.eval_mul,
           Polynomial.eval_ofNat, Polynomial.eval_X]; omega)
   convert hi using 1
   funext p
   rcases p with ⟨n, a⟩
   induction n with
   | zero => simp
   | succ n ih => simp only [Function.iterate_succ_apply', ← ih]; omega

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

namespace Block

 def encodeBitList {K : Type} (i o : K) : Block K := .loop i
   (.seq (readBit i o) (.push o false))

 theorem encodeBitList_exec {K : Type} [DecidableEq K] (w acc : List Bool) (z : Store K) :
    (encodeBitList inputPort outputPort).Exec (portStore w acc z)
      (portStore [] (w.foldl (fun acc b => false :: b :: acc) acc) z) (5 * w.length + 1) := by
   induction w generalizing acc with
   | nil => simpa [encodeBitList] using
       (Exec.loop_nil (a := .seq (readBit inputPort outputPort) (.push outputPort false))
         (rfl : portStore [] acc z inputPort = []))
   | cons b w ih =>
     have h₁ := readBit_exec b w acc z
     have h₂ : Exec (.push outputPort false) (portStore w (b :: acc) z)
         (portStore w (false :: b :: acc) z) 1 := by
       simpa only [portStore_output, update_output] using
         Exec.push outputPort false (portStore w (b :: acc) z)
     have he := Exec.loop_cons
       (show portStore (b :: w) acc z inputPort ≠ [] from List.cons_ne_nil _ _)
       (Exec.seq h₁ h₂) (ih (false :: b :: acc))
     simpa only [encodeBitList, List.foldl_cons, List.length_cons,
       show 5 * (w.length + 1) + 1 = 3 + 1 + (5 * w.length + 1) + 1 by omega] using he

end Block

 theorem fold_encodeBitList (w acc : List Bool) :
    w.foldl (fun acc b => false :: b :: acc) acc =
      (w.reverse.flatMap (fun b => [false, b])) ++ acc := by
  induction w generalizing acc with
  | nil => simp
  | cons b w ih =>
    simp only [List.foldl_cons, ih, List.reverse_cons, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc, List.cons_append, List.nil_append]

 theorem listCode_bit (w : List Bool) :
    listCode (fun b => [b]) w = w.flatMap (fun b => [false, b]) ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [listCode, List.flatMap_cons, List.cons_append,
      List.nil_append, ih]

namespace Poly

/-- Materialize the input encoding as an ordinary typed bit list. Each marker
and bit is written by charged finite-state stack code. -/
 theorem encoding {α : Type} [Coded α] : Poly (bits : α → List Bool) := by
   have hrev : RunsInPolyTime (bits : α → List Bool) (fun a => (bits a).reverse) _root_.id := by
     simpa only [List.reverse_reverse] using RunsInPolyTime.reverseEncoding (fun a : α => (bits a).reverse)
   have henc : RunsInPolyTime (fun a : α => (bits a).reverse) (bits : List Bool → List Bool)
       (bits : α → List Bool) := by
     let code : Block (Ports Unit) := .seq (.push outputPort true)
       (.loop inputPort (.seq (Block.readBit inputPort outputPort) (.push outputPort false)))
     refine ⟨Ports Unit, inferInstance, inputPort, outputPort, code, 5 * Polynomial.X + 2, ?_⟩
     intro a
     have hp : Block.Exec (.push outputPort true)
         (pairStore (bits a).reverse [] : Store (Ports Unit)) (pairStore (bits a).reverse [true]) 1 := by
       simpa only [pairStore, portStore_output, update_output] using
         Block.Exec.push (outputPort : Ports Unit) true (pairStore (bits a).reverse [])
     have hl := Block.encodeBitList_exec (bits a).reverse [true] (fun _ : Unit => [])
     rw [fold_encodeBitList, List.reverse_reverse, ← listCode_bit] at hl
     have he := Block.Exec.seq hp hl
     refine ⟨1 + (5 * (bits a).reverse.length + 1), ?_, ?_⟩
     · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]; omega
     · have he' : code.Exec (pairStore (bits a).reverse [])
           (pairStore [] (bits (bits a))) (1 + (5 * (bits a).reverse.length + 1)) := he
       simpa only [pairStore_input, pairStore_output] using he'
   exact henc.comp hrev

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 def compareBitsStep (s : List Bool × Bool) (x : Bool) : List Bool × Bool :=
   match s.1 with
   | [] => ([], false)
   | y :: ys => (ys, s.2 && decide (x = y))

 theorem compareBits_correct (xs ys : List Bool) (b : Bool) :
    let r := xs.foldl compareBitsStep (ys, b)
    (r.2 && r.1.isEmpty) = (b && decide (xs = ys)) := by
   induction xs generalizing ys b with
   | nil => cases ys <;> simp
   | cons x xs ih =>
     cases ys with
     | nil => simpa only [List.foldl_cons, compareBitsStep, List.cons_ne_nil,
         decide_false, Bool.and_false, Bool.false_and] using ih [] false
     | cons y ys =>
       simpa only [List.foldl_cons, compareBitsStep, List.cons.injEq, Bool.decide_and,
         Bool.and_assoc] using ih ys (b && decide (x = y))

 theorem compareBits_size (s : List Bool × Bool) (x : Bool) :
    bitSize (compareBitsStep s x) ≤ bitSize s := by
   obtain ⟨ys, b⟩ := s
   cases ys <;> simp [compareBitsStep, bitSize, bits_bool]

namespace Poly

 theorem compareBitsStep : Poly (fun p : (List Bool × Bool) × Bool =>
     Superstring.BitCode.compareBitsStep p.1 p.2) := by
   have hn : Poly (fun _ : Bool × Bool => (([] : List Bool), false)) := const ([], false)
   have hc : Poly (fun p : Bool × (List Bool × (Bool × Bool)) =>
       (p.2.1, p.2.2.1 && decide (p.2.2.2 = p.1))) :=
     (fst.comp snd).pair
       (and.comp ((fst.comp (snd.comp snd)).pair
         (eqBool.comp ((snd.comp (snd.comp snd)).pair fst))))
   have hp := (listCasesWith hn hc).comp
     ((fst.comp fst).pair ((snd.comp fst).pair (snd : Poly (Prod.snd : (List Bool × Bool) × Bool → Bool))))
   convert hp using 1
   funext p; rcases p with ⟨⟨ys, b⟩, x⟩; cases ys <;> rfl

 theorem eqBits : Poly (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
   have hf := foldl_additive compareBitsStep 0
     (fun s x => by simpa only [Polynomial.eval_zero, Nat.add_zero] using compareBits_size s x)
   have hp := (and.comp (snd.pair (isEmpty.comp fst))).comp
     (hf.comp (fst.pair (snd.pair (const true : Poly (fun _ : List Bool × List Bool => true)))))
   convert hp using 1
   funext p
   simpa only [Bool.true_and, Function.comp_apply] using (compareBits_correct p.1 p.2 true).symm

 theorem eq {α : Type} [Coded α] [DecidableEq α] :
     Poly (fun p : α × α => decide (p.1 = p.2)) := by
   have hp := eqBits.comp (((encoding : Poly (bits : α → List Bool)).comp
     (fst : Poly (Prod.fst : α × α → α))).pair (encoding.comp snd))
   convert hp using 1
   funext p
   change decide (p.1 = p.2) = decide (bits p.1 = bits p.2)
   congr 1
   exact propext Coded.injective.eq_iff.symm

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 theorem bitSize_map_le {α β : Type} [Coded β] (xs : List α) (f : α → β) (M : ℕ)
    (h : ∀ x ∈ xs, bitSize (f x) ≤ M) :
    bitSize (xs.map f) ≤ 1 + xs.length * (M + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hb := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, bitSize_cons, List.length_cons]
    nlinarith

 def mapWithStep {α β γ : Type} (f : γ × α → β) (s : γ × List β) (x : α) : γ × List β :=
   (s.1, f (s.1, x) :: s.2)

 theorem foldl_mapWithStep {α β γ : Type} (f : γ × α → β) (xs : List α)
    (c : γ) (out : List β) :
    xs.foldl (mapWithStep f) (c, out) = (c, (xs.map (fun x => f (c, x))).reverse ++ out) := by
  induction xs generalizing out with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, mapWithStep, ih, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append]

namespace Poly

 theorem mapWith {α β γ : Type} [Coded α] [Coded β] [Coded γ]
     {f : γ × α → β} (hf : Poly f) :
     Poly (fun p : γ × List α => p.2.map (fun x => f (p.1, x))) := by
   obtain ⟨P, hP⟩ := hf.output_size
   have hstep : Poly (fun p : (γ × List β) × α => mapWithStep f p.1 p.2) :=
     (fst.comp fst).pair (cons.comp ((hf.comp ((fst.comp fst).pair snd)).pair (snd.comp fst)))
   have hfold := foldl hstep (Polynomial.X + Polynomial.X * (P + 1) + 1) (by
     intro xs s j
     rcases s with ⟨c, out⟩
     rw [foldl_mapWithStep]
     let N := bitSize xs + (bitSize c + bitSize out)
     have hx : ∀ x ∈ xs.take j, bitSize (f (c, x)) ≤ P.eval N := by
       intro x hx
       apply (hP _).trans
       apply eval_mono_nat
       have hm := bitSize_mem (List.mem_of_mem_take hx)
       simp only [N, bitSize_prod]; omega
     have hm := bitSize_map_le (xs.take j) (fun x => f (c, x)) (P.eval N) hx
     have ha := bitSize_append ((xs.take j).map (fun x => f (c, x))).reverse out
     rw [bitSize_reverse] at ha
     have hl : (xs.take j).length ≤ N := by
       have h₁ := List.length_take_le' j xs
       have h₂ := length_le_bitSize xs
       simp only [N]; omega
     have hmul := Nat.mul_le_mul_right (P.eval N + 1) hl
     have hs : bitSize c + bitSize out ≤ N := by simp [N]
     simp only [bitSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
       Polynomial.eval_X, Polynomial.eval_one]
     change bitSize c + bitSize (((xs.take j).map (fun x => f (c, x))).reverse ++ out) ≤
       N + N * (P.eval N + 1) + 1
     omega)
   have hp := reverse.comp (snd.comp (hfold.comp (snd.pair
     (fst.pair (const ([] : List β) : Poly (fun _ : γ × List α => []))))))
   convert hp using 1
   funext p
   simp only [Function.comp_apply, foldl_mapWithStep, List.append_nil, List.reverse_reverse]

 theorem flatten {α : Type} [Coded α] : Poly (List.flatten : List (List α) → List α) := by
   have hs : ∀ (a x : List α), bitSize (a ++ x) ≤ bitSize a +
       (Polynomial.X : Polynomial ℕ).eval (bitSize x) := by
     intro a x
     have h := bitSize_append a x
     simp only [Polynomial.eval_X]; omega
   have hp := (foldl_additive append Polynomial.X hs).comp
     ((id : Poly (_root_.id : List (List α) → List (List α))).pair (const ([] : List α)))
   convert hp using 1
   funext xs
   simp only [Function.comp_apply, _root_.id]
   have he : ∀ a : List α, xs.foldl (· ++ ·) a = a ++ xs.flatten := by
     intro a
     induction xs generalizing a with
     | nil => simp
     | cons x xs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
   simpa only [List.nil_append] using (he []).symm

 theorem filter {α : Type} [Coded α] {p : α → Bool} (hp : Poly p) : Poly (List.filter p) := by
   have hc : Poly (fun x => if p x then [x] else []) :=
     ite hp (cons.comp (id.pair (const []))) (const [])
   have hf := flatten.comp (map hc)
   convert hf using 1
   funext xs
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [Function.comp_apply, List.map_cons, List.flatten_cons, List.filter_cons] at *
     by_cases hx : p x = true <;> simp [hx, ih]

 theorem filterWith {α γ : Type} [Coded α] [Coded γ] {p : γ × α → Bool}
     (hp : Poly p) : Poly (fun q : γ × List α => q.2.filter (fun x => p (q.1, x))) := by
   have hc : Poly (fun q : γ × α => if p q then [q.2] else []) :=
     ite hp (cons.comp (snd.pair (const []))) (const [])
   have hf := flatten.comp (mapWith hc)
   convert hf using 1
   funext q
   rcases q with ⟨c, xs⟩
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [Function.comp_apply, List.map_cons, List.flatten_cons, List.filter_cons] at *
     by_cases hx : p (c, x) = true <;> simp [hx, ih]

end Poly

end Superstring.BitCode

end OAI
