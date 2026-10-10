import OAI.Computability.Superstring.Parsing

namespace OAI

namespace Superstring.BitCode.RunsInPolyTime

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {f : α → β} {g : α → γ}

/-- Compute two values from the same explicitly coded input, then concatenate
their self-delimiting encodings. Duplication and concatenation are charged bitwise. -/
theorem pair (hf : RunsInPolyTime ea eb f) (hg : RunsInPolyTime ea ec g) :
    RunsInPolyTime ea (fun p : β × γ => eb p.1 ++ ec p.2) (fun a => (f a, g a)) := by
  obtain ⟨K, instK, i, o, b, P, hb⟩ := hf
  obtain ⟨L, instL, j, v, c, Q, hc⟩ := hg
  let input : (K ⊕ L) ⊕ Unit := .inl (.inl i)
  let ginput : (K ⊕ L) ⊕ Unit := .inl (.inr j)
  let foutput : (K ⊕ L) ⊕ Unit := .inl (.inl o)
  let output : (K ⊕ L) ⊕ Unit := .inl (.inr v)
  let scratch : (K ⊕ L) ⊕ Unit := .inr ()
  let code : Block ((K ⊕ L) ⊕ Unit) :=
    .seq (Block.copy input ginput scratch)
      (.seq ((b.rename Sum.inl).rename Sum.inl)
        (.seq ((c.rename Sum.inr).rename Sum.inl) (Block.move foutput output scratch)))
  let R : Polynomial ℕ := 17 * Polynomial.X + 9 * P + Q + 5
  refine ⟨(K ⊕ L) ⊕ Unit, inferInstance, input, output, code, R, ?_⟩
  intro a
  obtain ⟨n, hn, hf⟩ := hb a
  obtain ⟨m, hm, hg⟩ := hc a
  let s₀ := Sum.elim (Sum.elim (single i (ea a)) (single j (ea a))) (fun _ : Unit => [])
  let s₁ := Sum.elim (Sum.elim (single o (eb (f a))) (single j (ea a))) (fun _ : Unit => [])
  let s₂ := Sum.elim (Sum.elim (single o (eb (f a))) (single v (ec (g a)))) (fun _ : Unit => [])
  have hcopy := Block.copy_exec input ginput scratch (by simp [input, ginput])
    (by simp [input, scratch]) (by simp [ginput, scratch]) (single input (ea a))
    (by simp [single, input, scratch])
  have hi : single input (ea a) input = ea a := by simp [single]
  have hj : single input (ea a) ginput = [] := by simp [single, ginput, input]
  rw [hi, hj] at hcopy
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hcopy
  have he₀ : Function.update (single input (ea a)) ginput (ea a) = s₀ := by
    funext k
    rcases k with (k | k) | k
    · simp [input, ginput, s₀, single]
    · by_cases hk : k = j <;> simp [input, ginput, s₀, single, hk]
    · simp [input, ginput, s₀, single]
  rw [he₀] at hcopy
  have hf' : ((b.rename Sum.inl).rename Sum.inl).Exec s₀ s₁ n :=
    (hf.left (single j (ea a))).left (fun _ : Unit => [])
  have hg' : ((c.rename Sum.inr).rename Sum.inl).Exec s₁ s₂ m :=
    (hg.right (single o (eb (f a)))).left (fun _ : Unit => [])
  have hmove := Block.move_exec foutput output scratch (by simp [foutput, output])
    (by simp [foutput, scratch]) (by simp [output, scratch]) s₂ rfl
  have hfo : s₂ foutput = eb (f a) := by simp [s₂, foutput, single]
  have hgo : s₂ output = ec (g a) := by simp [s₂, output, single]
  rw [hfo, hgo] at hmove
  have he₂ : Function.update (Function.update s₂ foutput []) output (eb (f a) ++ ec (g a)) =
      single output (eb (f a) ++ ec (g a)) := by
    funext k
    rcases k with (k | k) | k
    · by_cases hk : k = o <;> simp only [s₂, foutput, output, single, Function.update_apply, Sum.elim, Sum.inl.injEq, reduceCtorEq, hk, ite_true, ite_false]
    · by_cases hk : k = v <;> simp only [s₂, foutput, output, single, Function.update_apply, Sum.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, hk, ite_true, ite_false]
    · simp only [s₂, foutput, output, single, Function.update_apply, Sum.elim, reduceCtorEq, ite_false]
  rw [he₂] at hmove
  refine ⟨9 * (ea a).length + 3 + (n + (m + (8 * (eb (f a)).length + 2))), ?_,
    Block.Exec.seq hcopy (Block.Exec.seq hf' (Block.Exec.seq hg' hmove))⟩
  have hlen := hf.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hlen
  simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

end Superstring.BitCode.RunsInPolyTime

namespace Superstring.BitCode

/-- Unary natural numbers have an explicit end marker, so prefix parsing never
relies on an uncharged register-length operation. -/
def natCode : ℕ → List Bool
  | 0 => [true]
  | n + 1 => false :: natCode n

@[simp] theorem length_natCode (n : ℕ) : (natCode n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natCode, List.length_cons, ih]

 theorem natCode_eq (n : ℕ) : natCode n = listCode (fun _ : Unit => []) (List.replicate n ()) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natCode, List.replicate_succ, listCode, List.nil_append, ih]

@[simp] theorem natCode_reverse (n : ℕ) : (natCode n).reverse = true :: List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [natCode, List.reverse_cons, ih, List.cons_append]
    exact congrArg (fun x => true :: x) (by
      simpa only [List.replicate_one] using (List.replicate_add n 1 false).symm)

 theorem Parses.nat : Parses natCode := by
  obtain ⟨K, inst, b, c, hb⟩ := (Parses.const []).list
  refine ⟨K, inst, b, c, ?_⟩
  intro n tail acc
  simpa only [← natCode_eq] using hb (List.replicate n ()) tail acc

namespace RunsInPolyTime

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

/-- Normalize any clean routine to the same input and output register. The
linear bit-order-preserving relocation is included in its polynomial clock. -/
theorem inPlace (hf : RunsInPolyTime ea eb f) :
    ∃ (K : Type) (_ : DecidableEq K) (i : K) (b : Block K) (P : Polynomial ℕ),
      ∀ a, ∃ n ≤ P.eval (ea a).length, b.Exec (single i (ea a)) (single i (eb (f a))) n := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := hf
  let code : Block (K ⊕ Unit) := .seq (b.rename Sum.inl)
    (Block.move (.inl o) (.inl i) (.inr ()))
  refine ⟨K ⊕ Unit, inferInstance, .inl i, code, 9 * P + 8 * Polynomial.X + 2, ?_⟩
  intro a
  obtain ⟨n, hn, hh⟩ := hb a
  have h₁ := hh.left (fun _ : Unit => [])
  simp only [single_left] at h₁
  have h₂ := Block.move_single (Sum.inl o : K ⊕ Unit) (.inl i) (.inr ())
    (by simp) (by simp) (eb (f a))
  refine ⟨n + (8 * (eb (f a)).length + 2), ?_, Block.Exec.seq h₁ h₂⟩
  have hs := hh.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

end RunsInPolyTime

namespace Block

variable {K : Type} [DecidableEq K] {α : Type} {e : α → List Bool} {f : α → α}

/-- Iterate a clean in-place routine once per explicitly stored counter bit.
The hypothesis is a STATE SIZE invariant, not an assumed time or computation
oracle. The only computation premise is an actual bit-program execution. -/
theorem iterate_exec (b : Block K) (i : K) (P : Polynomial ℕ)
    (hb : ∀ a, ∃ n ≤ P.eval (e a).length, b.Exec (single i (e a)) (single i (e (f a))) n)
    (n M : ℕ) (a : α) (hsize : ∀ j < n, (e (f^[j] a)).length ≤ M) :
    ∃ t ≤ n * (P.eval M + 2) + 1,
      (Block.loop (Sum.inr () : K ⊕ Unit) (.seq (.pop (.inr ())) (b.rename Sum.inl))).Exec
        (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate n false))
        (Sum.elim (single i (e (f^[n] a))) (fun _ : Unit => [])) t := by
  induction n generalizing a with
  | zero =>
    exact ⟨1, by simp, Exec.loop_nil rfl⟩
  | succ n ih =>
    have hrest : ∀ j < n, (e (f^[j] (f a))).length ≤ M := by
      intro j hj
      simpa only [← Function.iterate_succ_apply] using hsize (j + 1) (by omega)
    obtain ⟨m, hm, hrun⟩ := hb a
    obtain ⟨t, ht, htail⟩ := ih (f a) hrest
    have hpop : Exec (.pop (Sum.inr () : K ⊕ Unit))
        (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate (n + 1) false))
        (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate n false)) 1 := by
      have he : Function.update (fun _ : Unit => List.replicate (n + 1) false) ()
          (List.replicate (n + 1) false).tail = fun _ : Unit => List.replicate n false := by
        funext k; cases k; simp
      simpa only [Sum.elim_inr, update_right, he] using
        Exec.pop (Sum.inr () : K ⊕ Unit)
          (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate (n + 1) false))
    have hstep := hrun.left (fun _ : Unit => List.replicate n false)
    have hh := Exec.loop_cons (by simp only [Sum.elim_inr, List.replicate_succ, ne_eq,
      List.cons_ne_nil, not_false_eq_true]) (Exec.seq hpop hstep) htail
    refine ⟨1 + m + t + 1, ?_, ?_⟩
    · have hs := hsize 0 (by omega)
      simp only [Function.iterate_zero, _root_.id] at hs
      have hp := eval_mono_nat P hs
      nlinarith
    · simpa only [Function.iterate_succ_apply] using hh

end Block

end Superstring.BitCode

namespace Superstring.BitCode

/-- Place the parser's input in an existing work bank, its private storage in a
fresh bank, and its output in a fresh counter register. -/
def parserEmbedding {K L : Type} (i : K) : Ports L → (K ⊕ L) ⊕ Unit
  | .inl false => .inl (.inl i)
  | .inl true => .inr ()
  | .inr k => .inl (.inr k)

 theorem parserEmbedding_injective {K L : Type} (i : K) :
    Function.Injective (parserEmbedding (L := L) i) := by
  intro x y he
  rcases x with (x | x) <;> rcases y with (y | y)
  · cases x <;> cases y <;> simp_all only [parserEmbedding, reduceCtorEq]
  · cases x <;> simp only [parserEmbedding, Sum.inl.injEq, reduceCtorEq] at he
  · cases y <;> simp only [parserEmbedding, Sum.inl.injEq, reduceCtorEq] at he
  · simpa only [parserEmbedding, Sum.inl.injEq, Sum.inr.injEq] using he

namespace Block

 theorem Exec.parseAt {K L : Type} [DecidableEq K] [DecidableEq L]
    {b : Block (Ports L)} {x y u v : List Bool} {n : ℕ}
    (h : b.Exec (pairStore x u) (pairStore y v) n) (i : K) :
    (b.rename (parserEmbedding i)).Exec
      (Sum.elim (Sum.elim (single i x) (fun _ : L => [])) (fun _ : Unit => u))
      (Sum.elim (Sum.elim (single i y) (fun _ : L => [])) (fun _ : Unit => v)) n := by
  apply h.transport (parserEmbedding i) (parserEmbedding_injective i)
  · intro k
    cases k with
    | inl k => cases k <;> simp [parserEmbedding, pairStore, portStore, single]
    | inr k => rfl
  · intro k
    cases k with
    | inl k => cases k <;> simp [parserEmbedding, pairStore, portStore, single]
    | inr k => rfl
  · intro k hk
    rcases k with (k | k) | k
    · have hne : k ≠ i := by
        intro he
        exact hk (.inl false) (by simp [parserEmbedding, he])
      simp [single, hne]
    · rfl
    · cases k
      exact False.elim (hk (.inl true) rfl)

end Block

namespace RunsInPolyTime

/-- Bounded iteration of an actual polynomial bit routine is polynomial. The
bound is on encoded intermediate DATA, and the counter is explicitly unary.
This closure rule does not assume a polynomial-time evaluator or a time oracle. -/
theorem iterate {α : Type} {e : α → List Bool} {f : α → α}
    (hf : RunsInPolyTime e e f) (R : Polynomial ℕ)
    (hsize : ∀ n a j, j < n → (e (f^[j] a)).length ≤
      R.eval (natCode n ++ e a).length) :
    RunsInPolyTime (fun p : ℕ × α => natCode p.1 ++ e p.2) e
      (fun p => f^[p.1] p.2) := by
  obtain ⟨K, instK, i, b, P, hb⟩ := hf.inPlace
  obtain ⟨L, instL, parse, c, hp⟩ := Parses.nat
  let inp : (K ⊕ L) ⊕ Unit := .inl (.inl i)
  let counter : (K ⊕ L) ⊕ Unit := .inr ()
  let code : Block ((K ⊕ L) ⊕ Unit) :=
    .seq (parse.rename (parserEmbedding i))
      (.seq (.pop counter)
        (.loop counter (.seq (.pop counter) ((b.rename Sum.inl).rename Sum.inl))))
  let Q : Polynomial ℕ := Polynomial.C (c + 2) * (Polynomial.X + 1) +
    Polynomial.X * (P.comp R + 2) + 2
  refine ⟨(K ⊕ L) ⊕ Unit, inferInstance, inp, inp, code, Q, ?_⟩
  rintro ⟨n, a⟩
  let N := (natCode n ++ e a).length
  let M := R.eval N
  obtain ⟨t, ht, hparse⟩ := hp n (e a) []
  simp only [List.append_nil, natCode_reverse, length_natCode] at hparse ht
  have hparse' := hparse.parseAt i
  simp only [single_left] at hparse'
  have hb' : ∀ a, ∃ t ≤ P.eval (e a).length,
      (b.rename Sum.inl).Exec (single (Sum.inl i : K ⊕ L) (e a))
        (single (.inl i) (e (f a))) t := by
    intro a
    obtain ⟨t, ht, hh⟩ := hb a
    exact ⟨t, ht, by simpa only [single_left] using hh.left (fun _ : L => [])⟩
  have hpop : Block.Exec (.pop counter)
      (Sum.elim (single (Sum.inl i : K ⊕ L) (e a))
        (fun _ : Unit => true :: List.replicate n false))
      (Sum.elim (single (Sum.inl i : K ⊕ L) (e a))
        (fun _ : Unit => List.replicate n false)) 1 := by
    have he : Function.update (fun _ : Unit => true :: List.replicate n false) ()
        (List.replicate n false) = fun _ : Unit => List.replicate n false := by
      funext k; cases k; simp
    simpa only [counter, Sum.elim_inr, List.tail_cons, Block.update_right, he] using
      Block.Exec.pop counter (Sum.elim (single (Sum.inl i : K ⊕ L) (e a))
        (fun _ : Unit => true :: List.replicate n false))
  obtain ⟨u, hu, hloop⟩ := Block.iterate_exec (b.rename Sum.inl) (Sum.inl i : K ⊕ L)
    P hb' n M a (hsize n a)
  simp only [single_left] at hloop
  refine ⟨t + (1 + u), ?_, Block.Exec.seq hparse' (Block.Exec.seq hpop hloop)⟩
  have hn : n + 1 ≤ N := by simp only [N, List.length_append, length_natCode]; omega
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]
  change t + (1 + u) ≤ (c + 2) * (N + 1) + N * (P.eval M + 2) + 2
  have hm := Nat.mul_le_mul_right (P.eval M + 2) (show n ≤ N by omega)
  have ht' := ht.trans (Nat.mul_le_mul_left c (show n + 1 + 1 ≤ N + 1 by omega))
  nlinarith

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode

abbrev Workspace (K : Type) := Unit ⊕ K
abbrev workPort {K : Type} : Workspace K := .inl ()
def workStore {K : Type} (w : List Bool) (z : Store K) : Store (Workspace K) :=
  Sum.elim (fun _ => w) z

@[simp] theorem workStore_single {K : Type} [DecidableEq K] (w : List Bool) :
    workStore w (fun _ : K => []) = single workPort w := by
  funext k
  cases k with
  | inl k => cases k; simp [workStore, single, workPort]
  | inr k => simp [workStore, single, workPort]

 def workEmbedding {K : Type} [DecidableEq K] (i : K) (k : K) : Workspace K :=
   if k = i then workPort else .inr k

 theorem workEmbedding_injective {K : Type} [DecidableEq K] (i : K) :
     Function.Injective (workEmbedding i) := by
   intro x y he
   by_cases hx : x = i <;> by_cases hy : y = i
   · exact hx.trans hy.symm
   · simp only [workEmbedding, ite_eq_left hx, ite_eq_right hy, workPort, reduceCtorEq] at he
   · simp only [workEmbedding, ite_eq_right hx, ite_eq_left hy, workPort, reduceCtorEq] at he
   · exact Sum.inr.inj (by simpa only [workEmbedding, ite_eq_right hx, ite_eq_right hy] using he)

namespace Block

 theorem Exec.inWorkspace {K : Type} [DecidableEq K] {i : K}
    {b : Block K} {w v : List Bool} {n : ℕ}
    (h : b.Exec (single i w) (single i v) n) :
    (b.rename (workEmbedding i)).Exec
      (workStore w (fun _ : K => [])) (workStore v (fun _ : K => [])) n := by
  apply h.transport (workEmbedding i) (workEmbedding_injective i)
  · intro k
    by_cases hk : k = i <;> simp [workEmbedding, hk, workPort, workStore, single]
  · intro k
    by_cases hk : k = i <;> simp [workEmbedding, hk, workPort, workStore, single]
  · intro k hk
    cases k with
    | inl u =>
      cases u
      exact False.elim (hk i (by simp [workEmbedding, workPort]))
    | inr k => rfl

/-- Two in-place workspaces may share their data register, with all their
private registers disjoint. Everything outside the active workspace is framed. -/
theorem Exec.workspace {K L : Type} [DecidableEq K] [DecidableEq L]
    {b : Block (Workspace K)} {w v : List Bool} {n : ℕ}
    (h : b.Exec (workStore w (fun _ : K => [])) (workStore v (fun _ : K => [])) n)
    (f : K → L) (hf : Function.Injective f) (z : Store L) (hz : ∀ k, z (f k) = []) :
    (b.rename (Sum.map _root_.id f)).Exec (workStore w z) (workStore v z) n := by
  apply h.transport (Sum.map _root_.id f) (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩)
  · intro k
    cases k with
    | inl k => rfl
    | inr k => exact hz k
  · intro k
    cases k with
    | inl k => rfl
    | inr k => exact hz k
  · intro k hk
    cases k with
    | inl u => exact False.elim (hk (.inl u) rfl)
    | inr k => rfl

end Block

namespace RunsInPolyTime

 theorem canonical {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : RunsInPolyTime ea eb f) :
    ∃ (K : Type) (_ : DecidableEq K) (b : Block (Workspace K)) (P : Polynomial ℕ),
      ∀ a, ∃ n ≤ P.eval (ea a).length,
        b.Exec (workStore (ea a) (fun _ => [])) (workStore (eb (f a)) (fun _ => [])) n := by
  obtain ⟨K, inst, i, b, P, hb⟩ := h.inPlace
  refine ⟨K, inst, b.rename (workEmbedding i), P, ?_⟩
  intro a
  obtain ⟨n, hn, hh⟩ := hb a
  exact ⟨n, hn, hh.inWorkspace⟩

/-- Branch on an explicitly encoded Boolean, charging the branch and removal
of its bit. No unbounded predicate acts as a primitive instruction. -/
theorem boolCase {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f g : α → β} (hf : RunsInPolyTime ea eb f) (hg : RunsInPolyTime ea eb g) :
    RunsInPolyTime (fun p : Bool × α => p.1 :: ea p.2) eb
      (fun p => if p.1 then f p.2 else g p.2) := by
  obtain ⟨K, instK, b, P, hb⟩ := hf.canonical
  obtain ⟨L, instL, c, Q, hc⟩ := hg.canonical
  let bt : Block (Workspace (K ⊕ L)) := b.rename (Sum.map _root_.id Sum.inl)
  let bf : Block (Workspace (K ⊕ L)) := c.rename (Sum.map _root_.id Sum.inr)
  let code : Block (Workspace (K ⊕ L)) := .branch workPort .skip
    (.seq (.pop workPort) bf) (.seq (.pop workPort) bt)
  refine ⟨Workspace (K ⊕ L), inferInstance, workPort, workPort, code, P + Q + 2, ?_⟩
  rintro ⟨v, a⟩
  have hpop : Block.Exec (.pop workPort)
      (workStore (v :: ea a) (fun _ : K ⊕ L => []))
      (workStore (ea a) (fun _ : K ⊕ L => [])) 1 := by
    have he : Function.update (fun _ : Unit => v :: ea a) () (ea a) =
        fun _ : Unit => ea a := by funext k; cases k; simp
    simpa only [workStore, workPort, Sum.elim_inl, List.tail_cons,
      Block.update_left, he] using
      Block.Exec.pop (workPort : Workspace (K ⊕ L))
        (workStore (v :: ea a) (fun _ : K ⊕ L => []))
  cases v with
  | false =>
    obtain ⟨n, hn, hh⟩ := hc a
    have hrun := hh.workspace (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_false (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (c := .seq (.pop workPort) bt) rfl (Block.Exec.seq hpop hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hq : Q.eval (ea a).length ≤ Q.eval (false :: ea a).length :=
        eval_mono_nat Q (by simp)
      simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, Bool.false_eq_true, ↓reduceIte] using he
  | true =>
    obtain ⟨n, hn, hh⟩ := hb a
    have hrun := hh.workspace (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_true (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (b := .seq (.pop workPort) bf) rfl (Block.Exec.seq hpop hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hp : P.eval (ea a).length ≤ P.eval (true :: ea a).length :=
        eval_mono_nat P (by simp)
      simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, ↓reduceIte] using he

end RunsInPolyTime

end Superstring.BitCode

end OAI
