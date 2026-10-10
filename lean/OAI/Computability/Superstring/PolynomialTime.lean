import OAI.Computability.Superstring.Clock

namespace OAI

namespace Superstring.BitCode

/-- Actual code and a clock, not an oracle or a premise of the main theorem.
Ambient register types may be infinite names; certificate_any restricts them
exactly to finite support. All executions start and end with the single encoded
input/output stack. -/
def RunsInPolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) : Prop :=
  ∃ (K : Type) (_ : DecidableEq K) (i o : K) (b : Block K) (P : Polynomial ℕ),
    ∀ a, ∃ n ≤ P.eval (ea a).length,
      b.Exec (single i (ea a)) (single o (eb (f a))) n

namespace RunsInPolyTime

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {f : α → β} {g : β → γ}

theorem certificate (h : RunsInPolyTime ea eb f) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb f, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := h
  exact b.certificate_any ea eb f i o P hb

theorem output_length (h : RunsInPolyTime ea eb f) :
    ∃ P : Polynomial ℕ, ∀ a, (eb (f a)).length ≤ P.eval (ea a).length := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := h
  refine ⟨Polynomial.X + P, ?_⟩
  intro a
  obtain ⟨n, hn, hh⟩ := hb a
  have hl := hh.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hl
  simpa only [Polynomial.eval_add, Polynomial.eval_X] using hl.trans (Nat.add_le_add_left hn _)

theorem id (e : α → List Bool) : RunsInPolyTime e e id := by
  refine ⟨Unit, inferInstance, (), (), .skip, 1, ?_⟩
  intro a
  exact ⟨1, by simp, Block.Exec.skip _⟩

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode

variable {K L : Type} [DecidableEq K] [DecidableEq L]

@[simp] theorem single_left (i : K) (w : List Bool) :
    Sum.elim (single i w) (fun _ : L => []) = single (Sum.inl i) w := by
  funext k
  cases k with
  | inl k => simp [single]
  | inr k => simp [single]

@[simp] theorem single_right (i : L) (w : List Bool) :
    Sum.elim (fun _ : K => []) (single i w) = single (Sum.inr i) w := by
  funext k
  cases k with
  | inl k => simp [single]
  | inr k => simp [single]

namespace Block

theorem transfer_single (i j : K) (hij : i ≠ j) (w : List Bool) :
    (transfer i j).Exec (single i w) (single j w.reverse) (4 * w.length + 1) := by
  have hh := transfer_exec i j hij (single i w)
  have hi : single i w i = w := by simp [single]
  have hj : single i w j = [] := by simp [single, hij.symm]
  rw [hi, hj, List.append_nil] at hh
  have he : Function.update (Function.update (single i w) i []) j w.reverse = single j w.reverse := by
    funext k
    by_cases hk : k = j
    · subst k; simp [single]
    · by_cases hki : k = i
      · subst k; simp [single, hij]
      · simp [single, hk, hki]
  rw [he] at hh
  exact hh

/-- Relocate a single encoded value without reversing its bit order. -/
def move (i j scratch : K) : Block K := .seq (transfer i scratch) (transfer scratch j)

theorem move_single (i j scratch : K) (hi : i ≠ scratch) (hj : j ≠ scratch)
    (w : List Bool) : (move i j scratch).Exec (single i w) (single j w) (8 * w.length + 2) := by
  have hh := Exec.seq (transfer_single i scratch hi w) (transfer_single scratch j hj.symm w.reverse)
  simp only [List.reverse_reverse, List.length_reverse] at hh
  convert hh using 1 <;> first | rfl | omega


end Block

omit [DecidableEq K] [DecidableEq L] in
theorem eval_mono_nat (P : Polynomial ℕ) : Monotone P.eval := by
  intro n m h
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c => simp only [Polynomial.eval_monomial]; gcongr

namespace RunsInPolyTime

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {f : α → β} {g : β → γ}

/-- Composition of finite bit programs preserves polynomial-time computability. -/
theorem comp (hg : RunsInPolyTime eb ec g) (hf : RunsInPolyTime ea eb f) :
    RunsInPolyTime ea ec (g ∘ f) := by
  obtain ⟨K, instK, i, o, b, P, hb⟩ := hf
  obtain ⟨L, instL, j, v, c, Q, hc⟩ := hg
  let code : Block ((K ⊕ L) ⊕ Unit) :=
    .seq ((b.rename Sum.inl).rename Sum.inl)
      (.seq (Block.move (.inl (.inl o)) (.inl (.inr j)) (.inr ()))
        ((c.rename Sum.inr).rename Sum.inl))
  let R : Polynomial ℕ := P + (8 * (Polynomial.X + P) + 2) + Q.comp (Polynomial.X + P)
  refine ⟨(K ⊕ L) ⊕ Unit, inferInstance, .inl (.inl i), .inl (.inr v), code, R, ?_⟩
  intro a
  obtain ⟨n, hn, hf⟩ := hb a
  obtain ⟨m, hm, hg⟩ := hc (f a)
  have hl := hf.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hl
  have hout : (eb (f a)).length ≤ (ea a).length + P.eval (ea a).length :=
    hl.trans (Nat.add_le_add_left hn _)
  have hfirst := (hf.left (fun _ : L => [])).left (fun _ : Unit => [])
  have hlast := (hg.right (fun _ : K => [])).left (fun _ : Unit => [])
  simp only [single_left, single_right] at hfirst hlast
  have hmove := Block.move_single (Sum.inl (Sum.inl o) : (K ⊕ L) ⊕ Unit)
    (.inl (.inr j)) (.inr ()) Sum.inl_ne_inr Sum.inl_ne_inr (eb (f a))
  refine ⟨n + ((8 * (eb (f a)).length + 2) + m), ?_,
    Block.Exec.seq hfirst (Block.Exec.seq hmove hlast)⟩
  simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_comp]
  have hm' := hm.trans (eval_mono_nat Q hout)
  nlinarith

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode.RunsInPolyTime

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

/-- Turn an observed-output proof into clean composable code. No garbage is
silently ignored, and every extra clearing step is paid for. -/
theorem of_observed {K : Type} [DecidableEq K] (b : Block K) (i o : K)
    (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n t, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) t n ∧ t o = eb (f a)) : RunsInPolyTime ea eb f := by
  classical
  let l := ((insert i b.support).erase o).toList
  let code := Block.seq b (Block.clearMany l)
  let Q : Polynomial ℕ := P + Polynomial.C l.length * (2 * (Polynomial.X + P) + 1) + 1
  refine ⟨K, inferInstance, i, o, code, Q, ?_⟩
  intro a
  obtain ⟨n, t, hn, hrun, hout⟩ := correct a
  let N := (ea a).length
  have ht := (hrun.bounded N (single_bounded i (ea a))).mono (Nat.add_le_add_left hn N)
  obtain ⟨m, hm, hclear⟩ := Block.clearMany_exec l t (N + P.eval N) ht
  have hfinal : Block.cleared t l = single o (eb (f a)) := by
    funext k
    by_cases hko : k = o
    · subst k
      simp [Block.cleared, l, single, hout]
    · by_cases hk : k ∈ l
      · simp [Block.cleared, hk, single, hko]
      · have hnot : k ∉ insert i b.support := by
          intro hh
          apply hk
          simp only [l, Finset.mem_toList, Finset.mem_erase]
          exact ⟨hko, hh⟩
        have hi : k ≠ i := fun he => hnot (by simp [he])
        have hb : k ∉ b.support := fun he => hnot (Finset.mem_insert_of_mem he)
        have htk : t k = [] := by simpa only [single, ite_eq_right hi] using hrun.frame k hb
        simp only [Block.cleared, ite_eq_right hk, single, ite_eq_right hko, htk]
  rw [hfinal] at hclear
  refine ⟨n + m, ?_, Block.Exec.seq hrun hclear⟩
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
  exact (Nat.add_le_add hn hm).trans (by dsimp only [N]; omega)

theorem of_program {K : Type} [DecidableEq K] (p : Program K) (i o : K)
    (correct : ∀ a, (p.run (ea a).length (single i (ea a))) o = eb (f a)) :
    RunsInPolyTime ea eb f := by
  let b : Block (K ⊕ ℕ) := .seq (Block.copy (.inl i) (.inr 0) (.inr 1)) p.compile
  let P : Polynomial ℕ := 9 * Polynomial.X + 3 +
    13 * p.polynomial * (Polynomial.X + Polynomial.X + p.polynomial + 1)
  apply of_observed b (.inl i) (.inl o) P
  intro a
  let w := ea a
  let N := w.length
  let s := single i w
  let z : Store ℕ := single 0 w
  have hinit : Function.update (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) w =
      Sum.elim s z := by
    funext k
    cases k with
    | inl k => simp [s, single]
    | inr k => by_cases hk : k = 0 <;> simp [z, single, hk]
  have hcopy := Block.copy_exec (Sum.inl i : K ⊕ ℕ) (.inr 0) (.inr 1)
    Sum.inl_ne_inr Sum.inl_ne_inr (by simp) (single (.inl i) w)
    (by simp [single])
  have hin : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inl i) = w := by simp [single]
  have hout : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) = [] := by simp [single]
  rw [hin, hout] at hcopy
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hcopy
  rw [hinit] at hcopy
  have hz : Program.Clean p.depth z := by
    constructor
    · simp [z, single]
    · intro j _; simp [z, single]
  have hN : (z 0).length = N := by simp [z, single, N]
  obtain ⟨n, hn, hh⟩ := p.compile_exec N s N (single_bounded i w) z hz hN
  refine ⟨9 * N + 3 + n, Sum.elim (p.run N s) z, ?_, Block.Exec.seq hcopy hh, ?_⟩
  · simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, Program.eval_polynomial]
    exact Nat.add_le_add_left hn (9 * N + 3)
  · exact correct a

end Superstring.BitCode.RunsInPolyTime

namespace Superstring.BitCode.Block

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Embed a program into any injectively named register bank. Its entire
complement is framed. This also permits distinct routines to share designated
input/output registers while having disjoint private work registers. -/
theorem Exec.embed {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (f : K → L) (hf : Function.Injective f) (S : Store L)
    (hs : ∀ k, S (f k) = s k) :
    ∃ T, (b.rename f).Exec S T n ∧ (∀ k, T (f k) = t k) ∧
      ∀ j, (∀ k, f k ≠ j) → T j = S j := by
  induction h generalizing S with
  | push k x s =>
    refine ⟨Function.update S (f k) (x :: S (f k)), Exec.push _ _ _, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst j; simp [hs]
      · have hh : f j ≠ f k := fun he => hj (hf he)
        simp [hj, hh, hs]
    · intro j hj
      exact Function.update_of_ne (Ne.symm (hj k)) _ _
  | pop k s =>
    refine ⟨Function.update S (f k) (S (f k)).tail, Exec.pop _ _, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst j; simp [hs]
      · have hh : f j ≠ f k := fun he => hj (hf he)
        simp [hj, hh, hs]
    · intro j hj
      exact Function.update_of_ne (Ne.symm (hj k)) _ _
  | skip => exact ⟨S, Exec.skip S, hs, fun _ _ => rfl⟩
  | branch_none he _ ih =>
    obtain ⟨T, ht, hT, hframe⟩ := ih S hs
    exact ⟨T, Exec.branch_none (by rwa [hs]) ht, hT, hframe⟩
  | branch_false he _ ih =>
    obtain ⟨T, ht, hT, hframe⟩ := ih S hs
    exact ⟨T, Exec.branch_false (by rwa [hs]) ht, hT, hframe⟩
  | branch_true he _ ih =>
    obtain ⟨T, ht, hT, hframe⟩ := ih S hs
    exact ⟨T, Exec.branch_true (by rwa [hs]) ht, hT, hframe⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨T, ht, hT, htframe⟩ := ih₁ S hs
    obtain ⟨U, hu, hU, huframe⟩ := ih₂ T hT
    exact ⟨U, Exec.seq ht hu, hU, fun j hj => (huframe j hj).trans (htframe j hj)⟩
  | loop_nil he => exact ⟨S, Exec.loop_nil (by rwa [hs]), hs, fun _ _ => rfl⟩
  | loop_cons he _ _ ih₁ ih₂ =>
    obtain ⟨T, ht, hT, htframe⟩ := ih₁ S hs
    obtain ⟨U, hu, hU, huframe⟩ := ih₂ T hT
    exact ⟨U, Exec.loop_cons (by rwa [hs]) ht hu, hU,
      fun j hj => (huframe j hj).trans (htframe j hj)⟩

/-- The convenient exact-final-state form of framed register embedding. -/
theorem Exec.transport {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (f : K → L) (hf : Function.Injective f) (S T : Store L)
    (hs : ∀ k, S (f k) = s k) (ht : ∀ k, T (f k) = t k)
    (hframe : ∀ j, (∀ k, f k ≠ j) → T j = S j) :
    (b.rename f).Exec S T n := by
  obtain ⟨U, hu, hU, huframe⟩ := h.embed f hf S hs
  have he : U = T := by
    funext j
    by_cases hj : ∃ k, f k = j
    · obtain ⟨k, rfl⟩ := hj
      exact (hU k).trans (ht k).symm
    · have hj' : ∀ k, f k ≠ j := by simpa only [not_exists] using hj
      exact (huframe j hj').trans (hframe j hj').symm
  rwa [he] at hu

end Superstring.BitCode.Block

end OAI
