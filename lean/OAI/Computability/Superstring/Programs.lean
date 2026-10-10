import OAI.Computability.Superstring.Instructions

namespace OAI

namespace Superstring.BitCode.Block

variable {K : Type} [DecidableEq K]

/-- Clearing and transfers are explicit bit programs. In particular, reversing
or copying a variable-width label is never given unit cost. -/
def clear (k : K) : Block K := .loop k (.pop k)

def transfer (i j : K) : Block K := .loop i
  (.branch i .skip (.seq (.pop i) (.push j false)) (.seq (.pop i) (.push j true)))

theorem clear_exec (k : K) (s : Store K) :
    (clear k).Exec s (Function.update s k []) (2 * (s k).length + 1) := by
  generalize he : s k = w
  induction w generalizing s with
  | nil =>
    have hx : Function.update s k [] = s := by rw [← he, Function.update_eq_self]
    rw [hx]
    exact .loop_nil he
  | cons x xs ih =>
    let t := Function.update s k xs
    have ht : t k = xs := Function.update_self _ _ _
    have hbody : Exec (.pop k) s t 1 := by
      simpa only [he, List.tail_cons, t] using Exec.pop k s
    have hrest := ih t ht
    have hu : Function.update t k [] = Function.update s k [] := Function.update_idem _ _ _
    have hh := Exec.loop_cons (by simp [he]) hbody hrest
    rw [hu] at hh
    rw [show 2 * (x :: xs).length + 1 = 1 + (2 * xs.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    exact hh

theorem transfer_exec (i j : K) (hne : i ≠ j) (s : Store K) :
    (transfer i j).Exec s
      (Function.update (Function.update s i []) j ((s i).reverse ++ s j))
      (4 * (s i).length + 1) := by
  generalize he : s i = w
  induction w generalizing s with
  | nil =>
    have hx : Function.update (Function.update s i []) j (List.reverse [] ++ s j) = s := by
      simp only [List.reverse_nil, List.nil_append]
      rw [← he, Function.update_eq_self, Function.update_eq_self]
    rw [hx]
    exact .loop_nil he
  | cons x xs ih =>
    let t := Function.update (Function.update s i xs) j (x :: s j)
    have ht : t i = xs := by simp [t, hne]
    have htj : t j = x :: s j := Function.update_self _ _ _
    have hpop : Exec (.pop i) s (Function.update s i xs) 1 := by
      simpa only [he, List.tail_cons] using Exec.pop i s
    have hpush : Exec (.push j x) (Function.update s i xs) t 1 := by
      simpa only [Function.update_of_ne hne.symm, t] using Exec.push j x (Function.update s i xs)
    have hbody : Exec
        (.branch i .skip (.seq (.pop i) (.push j false)) (.seq (.pop i) (.push j true))) s t 3 := by
      cases x with
      | false => exact .branch_false (by simp [he]) (.seq hpop hpush)
      | true => exact .branch_true (by simp [he]) (.seq hpop hpush)
    have hrest := ih t ht
    rw [htj] at hrest
    have hu : Function.update (Function.update t i []) j (xs.reverse ++ x :: s j) =
        Function.update (Function.update s i []) j ((x :: xs).reverse ++ s j) := by
      funext k
      by_cases hik : k = i
      · subst k
        simp [hne]
      · by_cases hjk : k = j
        · subst k
          simp [List.reverse_cons, List.append_assoc]
        · simp [t, hik, hjk]
    have hh := Exec.loop_cons (by simp [he]) hbody hrest
    rw [hu] at hh
    rw [show 4 * (x :: xs).length + 1 = 3 + (4 * xs.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    exact hh

end Superstring.BitCode.Block

namespace Superstring.BitCode.Block

variable {K : Type} [DecidableEq K]


def fanout (i j k : K) : Block K := .loop i (.branch i .skip
  (.seq (.pop i) (.seq (.push j false) (.push k false)))
  (.seq (.pop i) (.seq (.push j true) (.push k true))))

theorem fanout_exec (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s : Store K) : (fanout i j k).Exec s
      (Function.update (Function.update (Function.update s i [])
        j ((s i).reverse ++ s j)) k ((s i).reverse ++ s k))
      (5 * (s i).length + 1) := by
  generalize he : s i = w
  induction w generalizing s with
  | nil =>
    have hx : Function.update (Function.update (Function.update s i [])
        j (List.reverse [] ++ s j)) k (List.reverse [] ++ s k) = s := by
      simp only [List.reverse_nil, List.nil_append]
      rw [← he, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
    rw [hx]
    exact .loop_nil he
  | cons x xs ih =>
    let t := Function.update (Function.update (Function.update s i xs) j (x :: s j)) k (x :: s k)
    have ht : t i = xs := by simp [t, hij, hik]
    have htj : t j = x :: s j := by simp [t, hjk]
    have htk : t k = x :: s k := Function.update_self _ _ _
    have hp : Exec (.pop i) s (Function.update s i xs) 1 := by
      simpa only [he, List.tail_cons] using Exec.pop i s
    have hj : Exec (.push j x) (Function.update s i xs)
        (Function.update (Function.update s i xs) j (x :: s j)) 1 := by
      simpa only [Function.update_of_ne hij.symm] using Exec.push j x (Function.update s i xs)
    have hk : Exec (.push k x) (Function.update (Function.update s i xs) j (x :: s j)) t 1 := by
      simpa only [Function.update_of_ne hjk.symm, Function.update_of_ne hik.symm, t]
        using Exec.push k x (Function.update (Function.update s i xs) j (x :: s j))
    have hbody : Exec (.branch i .skip
        (.seq (.pop i) (.seq (.push j false) (.push k false)))
        (.seq (.pop i) (.seq (.push j true) (.push k true)))) s t 4 := by
      cases x with
      | false => exact .branch_false (by simp [he]) (.seq hp (.seq hj hk))
      | true => exact .branch_true (by simp [he]) (.seq hp (.seq hj hk))
    have hrest := ih t ht
    rw [htj, htk] at hrest
    have hu : Function.update (Function.update (Function.update t i [])
        j (xs.reverse ++ x :: s j)) k (xs.reverse ++ x :: s k) =
        Function.update (Function.update (Function.update s i [])
        j ((x :: xs).reverse ++ s j)) k ((x :: xs).reverse ++ s k) := by
      funext l
      by_cases hli : l = i
      · subst l; simp [hij, hik]
      · by_cases hlj : l = j
        · subst l; simp [hjk, List.reverse_cons, List.append_assoc]
        · by_cases hlk : l = k
          · subst l; simp [List.reverse_cons, List.append_assoc]
          · simp [t, hli, hlj, hlk]
    have hh := Exec.loop_cons (by simp [he]) hbody hrest
    rw [hu] at hh
    rw [show 5 * (x :: xs).length + 1 = 4 + (5 * xs.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    exact hh


def copy (i j t : K) : Block K :=
  .seq (clear j) (.seq (transfer i t) (fanout t i j))

theorem copy_exec (i j t : K) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (s : Store K) (ht : s t = []) : (copy i j t).Exec s
      (Function.update s j (s i)) (2 * (s j).length + 9 * (s i).length + 3) := by
  let s₁ := Function.update s j []
  let s₂ := Function.update (Function.update s₁ i []) t ((s₁ i).reverse ++ s₁ t)
  have h₁ := clear_exec j s
  have h₂ := transfer_exec i t hit s₁
  have h₃ := fanout_exec t i j hit.symm hjt.symm hij s₂
  have hi₁ : s₁ i = s i := Function.update_of_ne hij _ _
  have ht₁ : s₁ t = [] := by simp [s₁, hjt.symm, ht]
  have ht₂ : s₂ t = (s i).reverse := by simp [s₂, hi₁, ht₁]
  have hi₂ : s₂ i = [] := by simp [s₂, hit]
  have hj₂ : s₂ j = [] := by simp [s₂, s₁, hjt, hij.symm]
  simp only [ht₂, hi₂, hj₂, List.append_nil, List.reverse_reverse, List.length_reverse] at h₃
  have hfinal : Function.update (Function.update (Function.update s₂ t []) i (s i)) j (s i) =
      Function.update s j (s i) := by
    funext l
    by_cases hlj : l = j
    · subst l; simp
    · by_cases hli : l = i
      · subst l; simp [hij]
      · by_cases hlt : l = t
        · subst l; simp [hjt.symm, hit.symm, ht]
        · simp [s₂, s₁, hlj, hli, hlt]
  rw [hfinal] at h₃
  have hh := Exec.seq h₁ (Exec.seq h₂ h₃)
  rw [hi₁] at hh
  convert hh using 1 <;> first | rfl | omega

end Superstring.BitCode.Block

namespace Superstring.BitCode.Block

variable {K L : Type}

/-- Change the names of registers; loops and instructions are unchanged. -/
def rename (f : K → L) : Block K → Block L
  | .push k b => .push (f k) b
  | .pop k => .pop (f k)
  | .skip => .skip
  | .branch k a b c => .branch (f k) (a.rename f) (b.rename f) (c.rename f)
  | .seq a b => .seq (a.rename f) (b.rename f)
  | .loop k a => .loop (f k) (a.rename f)

/-- A syntax tree mentions only finitely many registers. -/
def support [DecidableEq K] : Block K → Finset K
  | .push k _ | .pop k => {k}
  | .skip => ∅
  | .branch k a b c => insert k (a.support ∪ b.support ∪ c.support)
  | .seq a b => a.support ∪ b.support
  | .loop k a => insert k a.support

theorem update_comp [DecidableEq K] [DecidableEq L] (g : L → K)
    (hg : Function.Injective g) (s : Store K) (j : L) (w : List Bool) :
    Function.update s (g j) w ∘ g = Function.update (s ∘ g) j w := by
  funext i
  by_cases h : i = j
  · subst i; simp
  · have hh : g i ≠ g j := fun he => h (hg he)
    simp [h, hh]

/-- Restrict an execution to any injective family of registers containing all
registers in its syntax. The rest of an infinite ambient store is irrelevant. -/
theorem Exec.pullback [DecidableEq K] [DecidableEq L] (f : K → L) (g : L → K)
    (hg : Function.Injective g) {b : Block K} {s t : Store K} {n : ℕ}
    (h : b.Exec s t n) (hf : ∀ k ∈ b.support, g (f k) = k) :
    (b.rename f).Exec (s ∘ g) (t ∘ g) n := by
  induction h with
  | push k v s =>
    have hk := hf k (by simp [support])
    have hu (w : List Bool) : Function.update s k w ∘ g =
        Function.update (s ∘ g) (f k) w := by
      simpa only [hk] using update_comp g hg s (f k) w
    rw [hu]
    simpa only [rename, Function.comp_apply, hk] using Exec.push (f k) v (s ∘ g)
  | pop k s =>
    have hk := hf k (by simp [support])
    have hu (w : List Bool) : Function.update s k w ∘ g =
        Function.update (s ∘ g) (f k) w := by
      simpa only [hk] using update_comp g hg s (f k) w
    rw [hu]
    simpa only [rename, Function.comp_apply, hk] using Exec.pop (f k) (s ∘ g)
  | skip s => exact .skip _
  | @branch_none k a b c s t n hh h ih =>
    apply Exec.branch_none
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih (fun k hk => hf k (by simp [support, hk]))
  | @branch_false k a b c s t n hh h ih =>
    apply Exec.branch_false
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih (fun k hk => hf k (by simp [support, hk]))
  | @branch_true k a b c s t n hh h ih =>
    apply Exec.branch_true
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih (fun k hk => hf k (by simp [support, hk]))
  | seq h₁ h₂ ih₁ ih₂ =>
    exact .seq (ih₁ (fun k hk => hf k (by simp [support, hk])))
      (ih₂ (fun k hk => hf k (by simp [support, hk])))
  | @loop_nil k a s hh =>
    apply Exec.loop_nil
    simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
  | @loop_cons k a s t u m n hh h₁ h₂ ih₁ ih₂ =>
    apply Exec.loop_cons
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih₁ (fun k hk => hf k (by simp [support, hk]))
    · exact ih₂ hf

end Superstring.BitCode.Block

namespace Superstring.BitCode

/-- A bounded-loop register language. Every `repeat` uses the ORIGINAL input
length, not a mutable register. Nesting is static in the finite program. Copy is
assignment, not concatenation; the only operation increasing maximum word length
is a one-bit push. This gives uniform polynomial bounds for every program. -/
inductive Program (K : Type)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | clear (k : K)
  | copy (source target : K)
  | skip
  | branch (k : K) (empty low high : Program K)
  | seq (first second : Program K)
  | repeat (body : Program K)

namespace Program

variable {K : Type} [DecidableEq K]

def run (N : ℕ) : Program K → Store K → Store K
  | .push k b, s => Function.update s k (b :: s k)
  | .pop k, s => Function.update s k (s k).tail
  | .clear k, s => Function.update s k []
  | .copy i j, s => Function.update s j (s i)
  | .skip, s => s
  | .branch k a b c, s => match (s k).head? with
    | none => a.run N s
    | some false => b.run N s
    | some true => c.run N s
  | .seq a b, s => b.run N (a.run N s)
  | .repeat a, s => (a.run N)^[N] s

def work (N : ℕ) : Program K → ℕ
  | .push _ _ | .pop _ | .clear _ | .copy _ _ | .skip => 1
  | .branch _ a b c => 1 + a.work N + b.work N + c.work N
  | .seq a b => a.work N + b.work N
  | .repeat a => (N + 1) * (a.work N + 1)

noncomputable def polynomial : Program K → Polynomial ℕ
  | .push _ _ | .pop _ | .clear _ | .copy _ _ | .skip => 1
  | .branch _ a b c => 1 + a.polynomial + b.polynomial + c.polynomial
  | .seq a b => a.polynomial + b.polynomial
  | .repeat a => (Polynomial.X + 1) * (a.polynomial + 1)

omit [DecidableEq K] in
theorem eval_polynomial (p : Program K) (N : ℕ) : p.polynomial.eval N = p.work N := by
  induction p <;> simp_all [polynomial, work]

omit [DecidableEq K] in
theorem work_pos (p : Program K) (N : ℕ) : 0 < p.work N := by
  induction p <;> simp_all [work]

/-- All stack lengths are bounded by a common number. -/
def Bounded (s : Store K) (M : ℕ) : Prop := ∀ k, (s k).length ≤ M

omit [DecidableEq K] in
theorem Bounded.mono {s : Store K} {M M' : ℕ} (h : Bounded s M) (hh : M ≤ M') :
    Bounded s M' := fun k => (h k).trans hh

theorem Bounded.update {s : Store K} {M : ℕ} (h : Bounded s M) (k : K)
    (w : List Bool) (hw : w.length ≤ M) : Bounded (Function.update s k w) M := by
  intro j
  by_cases hj : j = k
  · subst j; simpa using hw
  · simpa [hj] using h j

omit [DecidableEq K] in
theorem iterate_bounded (f : Store K → Store K) (w : ℕ)
    (h : ∀ s M, Bounded s M → Bounded (f s) (M + w))
    (s : Store K) (M n : ℕ) (hs : Bounded s M) :
    Bounded (f^[n] s) (M + n * w) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := h (f^[n] s) (M + n * w) ih
    simpa only [Nat.succ_mul, Nat.add_assoc] using hh

theorem run_bounded (p : Program K) (N : ℕ) (s : Store K) (M : ℕ)
    (hs : Bounded s M) : Bounded (p.run N s) (M + p.work N) := by
  induction p generalizing s M with
  | push k b =>
    change Bounded (Function.update s k (b :: s k)) (M + 1)
    exact (hs.mono (Nat.le_add_right M 1)).update k (b :: s k)
      (by simpa only [List.length_cons] using Nat.succ_le_succ (hs k))
  | pop k =>
    change Bounded (Function.update s k (s k).tail) (M + 1)
    exact (hs.mono (Nat.le_add_right M 1)).update k (s k).tail
      (by simp only [List.length_tail]; have := hs k; omega)
  | clear k =>
    exact (hs.mono (Nat.le_add_right M 1)).update k [] (by simp)
  | copy i j =>
    exact (hs.mono (Nat.le_add_right M 1)).update j (s i) ((hs i).trans (Nat.le_add_right M 1))
  | skip => exact hs.mono (Nat.le_add_right M 1)
  | branch k a b c iha ihb ihc =>
    dsimp only [run]
    cases hh : (s k).head? with
    | none => exact (iha s M hs).mono (by change M + a.work N ≤ M + (1 + a.work N + b.work N + c.work N); omega)
    | some q => cases q with
      | false => exact (ihb s M hs).mono (by change M + b.work N ≤ M + (1 + a.work N + b.work N + c.work N); omega)
      | true => exact (ihc s M hs).mono (by change M + c.work N ≤ M + (1 + a.work N + b.work N + c.work N); omega)
  | seq a b iha ihb =>
    have hh := ihb (a.run N s) (M + a.work N) (iha s M hs)
    simpa only [run, work, Nat.add_assoc] using hh
  | «repeat» a ih =>
    have hh := iterate_bounded (a.run N) (a.work N) ih s M N hs
    exact hh.mono (by change M + N * a.work N ≤ M + ((N + 1) * (a.work N + 1)); nlinarith)

/-- Only the maximum loop-nesting depth determines the number of counters. -/
def depth : Program K → ℕ
  | .push _ _ | .pop _ | .clear _ | .copy _ _ | .skip => 0
  | .branch _ a b c => max a.depth (max b.depth c.depth)
  | .seq a b => max a.depth b.depth
  | .repeat a => a.depth + 1


def compile : Program K → Block (K ⊕ ℕ)
  | .push k b => .push (.inl k) b
  | .pop k => .pop (.inl k)
  | .clear k => Block.clear (.inl k)
  | .copy i j => if i = j then .skip else Block.copy (.inl i) (.inl j) (.inr 1)
  | .skip => .skip
  | .branch k a b c => .branch (.inl k) a.compile b.compile c.compile
  | .seq a b => .seq a.compile b.compile
  | .repeat a => .seq (Block.copy (.inr 0) (.inr (a.depth + 2)) (.inr 1))
      (.loop (.inr (a.depth + 2)) (.seq (.pop (.inr (a.depth + 2))) a.compile))

/-- Unused higher counters may contain arbitrary data, for compositional use. -/
def Clean (d : ℕ) (z : Store ℕ) : Prop := z 1 = [] ∧ ∀ j < d, z (j + 2) = []

theorem Clean.mono {d e : ℕ} {z : Store ℕ} (hz : Clean e z) (h : d ≤ e) : Clean d z :=
  ⟨hz.1, fun j hj => hz.2 j (lt_of_lt_of_le hj h)⟩

theorem Clean.update_above {d e : ℕ} {z : Store ℕ} (hz : Clean d z) (h : d ≤ e)
    (w : List Bool) : Clean d (Function.update z (e + 2) w) := by
  constructor
  · simp [hz.1]
  · intro j hj
    rw [Function.update_of_ne (by omega)]
    exact hz.2 j hj

@[simp] theorem sum_update_left (s : Store K) (z : Store ℕ) (k : K) (w : List Bool) :
    Function.update (Sum.elim s z) (.inl k) w = Sum.elim (Function.update s k w) z := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [h]
  | inr j => simp

@[simp] theorem sum_update_right (s : Store K) (z : Store ℕ) (k : ℕ) (w : List Bool) :
    Function.update (Sum.elim s z) (.inr k) w = Sum.elim s (Function.update z k w) := by
  funext j
  cases j with
  | inl j => simp
  | inr j => by_cases h : j = k <;> simp [h]

end Program

end Superstring.BitCode

end OAI
