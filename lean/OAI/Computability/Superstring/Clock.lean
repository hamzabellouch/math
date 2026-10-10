import OAI.Computability.Superstring.Programs

namespace OAI

namespace Superstring.BitCode.Program

variable {K : Type} [DecidableEq K]

/-- Execute a reserved loop counter, with a uniform bound for each body call.
There is no test of an arbitrary predicate: only this counter is tested. -/
theorem counter_loop (b : Block (K ⊕ ℕ)) (f : Store K → Store K)
    (d N M C : ℕ)
    (hb : ∀ s z, Clean d z → (z 0).length = N → Bounded s M →
      ∃ n ≤ C, b.Exec (Sum.elim s z) (Sum.elim (f s) z) n)
    (s : Store K) (z : Store ℕ) (hz : Clean d z) (hN : (z 0).length = N)
    (hinv : ∀ i ≤ (z (d + 2)).length, Bounded (f^[i] s) M) :
    ∃ n ≤ (z (d + 2)).length * (C + 2) + 1,
      (Block.loop (.inr (d + 2)) (.seq (.pop (.inr (d + 2))) b)).Exec
        (Sum.elim s z)
        (Sum.elim (f^[(z (d + 2)).length] s) (Function.update z (d + 2) [])) n := by
  generalize he : z (d + 2) = w at *
  induction w generalizing s z with
  | nil =>
    have hu : Function.update z (d + 2) [] = z := by rw [← he, Function.update_eq_self]
    refine ⟨1, by simp, ?_⟩
    simpa only [List.length_nil, Function.iterate_zero, id_eq, hu] using
      (Block.Exec.loop_nil (a := Block.seq (.pop (.inr (d + 2))) b)
        (show (Sum.elim s z) (.inr (d + 2)) = [] from he))
  | cons x xs ih =>
    let z' := Function.update z (d + 2) xs
    have hz' : Clean d z' := hz.update_above le_rfl xs
    have hN' : (z' 0).length = N := by simpa only [z', Function.update_of_ne (show (0 : ℕ) ≠ d + 2 by omega)] using hN
    have hhead : Bounded s M := by simpa using hinv 0 (by omega)
    obtain ⟨n, hn, hh⟩ := hb s z' hz' hN' hhead
    have hpop : Block.Exec (.pop (.inr (d + 2))) (Sum.elim s z) (Sum.elim s z') 1 := by
      simpa only [Sum.elim_inr, he, List.tail_cons, sum_update_right, z'] using
        Block.Exec.pop (.inr (d + 2)) (Sum.elim s z)
    have htail : ∀ i ≤ xs.length, Bounded (f^[i] (f s)) M := by
      intro i hi
      rw [← Function.iterate_succ_apply]
      apply hinv
      simp only [List.length_cons]
      omega
    obtain ⟨m, hm, hrest⟩ := ih (f s) z' hz' hN' (Function.update_self _ _ _) htail
    have hresult := Block.Exec.loop_cons
      (show (Sum.elim s z) (.inr (d + 2)) ≠ [] by simp [he])
      (Block.Exec.seq hpop hh) hrest
    refine ⟨1 + n + m + 1, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa only [z', Function.update_idem, List.length_cons, Function.iterate_succ_apply]
        using hresult

end Superstring.BitCode.Program

namespace Superstring.BitCode.Program

/-- Uniform bit clock; the polynomial work counts syntactic bounded iterations. -/
def clock (w N M : ℕ) : ℕ := 13 * w * (M + N + w + 1)

theorem clock_add (a b N M : ℕ) :
    clock a N M + clock b N (M + a) ≤ clock (a + b) N M := by
  dsimp only [clock]
  nlinarith

theorem clock_step {a b : ℕ} (h : a + 1 ≤ b) (N M : ℕ) :
    clock a N M + 1 ≤ clock b N M := by
  dsimp only [clock]
  nlinarith [Nat.mul_le_mul_right (M + N + a + 1) h,
    Nat.mul_le_mul_left b (show M + N + a + 1 ≤ M + N + b + 1 by omega)]

theorem clock_loop (w N M : ℕ) :
    9 * N + 3 + (N * (clock w N (M + N * w) + 2) + 1) ≤
      clock ((N + 1) * (w + 1)) N M := by
  let W := (N + 1) * (w + 1)
  let B := M + N + W + 1
  have hW : N * w + w ≤ W := by dsimp [W]; nlinarith
  have h₁ : clock w N (M + N * w) ≤ 13 * w * B := by
    apply Nat.mul_le_mul_left
    dsimp only [B]
    omega
  have h₂ : 11 * N + 4 ≤ 13 * (N + 1) * B := by
    have hB : 1 ≤ B := by dsimp [B]; omega
    nlinarith [Nat.mul_le_mul_left (13 * (N + 1)) hB]
  have h₃ : N * w + (N + 1) ≤ W := by dsimp [W]; nlinarith
  calc
    _ ≤ 9 * N + 3 + (N * (13 * w * B + 2) + 1) := by gcongr
    _ = 13 * (N * w) * B + (11 * N + 4) := by ring
    _ ≤ 13 * (N * w) * B + 13 * (N + 1) * B := Nat.add_le_add_left h₂ _
    _ = 13 * (N * w + (N + 1)) * B := by ring
    _ ≤ 13 * W * B := by gcongr

variable {K : Type} [DecidableEq K]

/-- Complete correctness and a polynomial bit-clock for bounded-loop programs. -/
theorem compile_exec (p : Program K) (N : ℕ) (s : Store K) (M : ℕ)
    (hs : Bounded s M) (z : Store ℕ) (hz : Clean p.depth z)
    (hN : (z 0).length = N) :
    ∃ n ≤ clock (p.work N) N M,
      p.compile.Exec (Sum.elim s z) (Sum.elim (p.run N s) z) n := by
  induction p generalizing s M z with
  | push k v =>
    refine ⟨1, by simp [work, clock]; omega, ?_⟩
    simpa only [compile, run, Sum.elim_inl, sum_update_left] using
      Block.Exec.push (.inl k) v (Sum.elim s z)
  | pop k =>
    refine ⟨1, by simp [work, clock]; omega, ?_⟩
    simpa only [compile, run, Sum.elim_inl, sum_update_left] using
      Block.Exec.pop (.inl k) (Sum.elim s z)
  | clear k =>
    refine ⟨2 * (s k).length + 1, ?_, ?_⟩
    · have := hs k
      simp only [work, clock]
      omega
    · simpa only [compile, run, Sum.elim_inl, sum_update_left] using
        Block.clear_exec (.inl k) (Sum.elim s z)
  | copy i j =>
    by_cases hij : i = j
    · subst j
      refine ⟨1, by simp [work, clock]; omega, ?_⟩
      simpa [compile, run] using
        Block.Exec.skip (Sum.elim s z)
    · refine ⟨2 * (s j).length + 9 * (s i).length + 3, ?_, ?_⟩
      · have := hs i
        have := hs j
        simp only [work, clock]
        omega
      · simpa only [compile, ite_eq_right hij, run, Sum.elim_inl, sum_update_left] using
          Block.copy_exec (Sum.inl i : K ⊕ ℕ) (.inl j) (.inr 1) (by simpa using hij)
            (by simp) (by simp) (Sum.elim s z) hz.1
  | skip =>
    exact ⟨1, by simp [work, clock]; omega, Block.Exec.skip _⟩
  | branch k a b c iha ihb ihc =>
    have ha := hz.mono (le_max_left _ _)
    have hb := hz.mono ((le_max_left _ _).trans (le_max_right _ _))
    have hc := hz.mono ((le_max_right _ _).trans (le_max_right _ _))
    cases hh : (s k).head? with
    | none =>
      obtain ⟨n, hn, hrun⟩ := iha s M hs z ha hN
      refine ⟨n + 1, (Nat.add_le_add_right hn 1).trans (clock_step (by dsimp [work]; omega) N M), ?_⟩
      simpa only [compile, run, hh] using Block.Exec.branch_none (k := Sum.inl k)
        (b := b.compile) (c := c.compile) hh hrun
    | some q => cases q with
      | false =>
        obtain ⟨n, hn, hrun⟩ := ihb s M hs z hb hN
        refine ⟨n + 1, (Nat.add_le_add_right hn 1).trans (clock_step (by dsimp [work]; omega) N M), ?_⟩
        simpa only [compile, run, hh] using Block.Exec.branch_false (k := Sum.inl k)
          (a := a.compile) (c := c.compile) hh hrun
      | true =>
        obtain ⟨n, hn, hrun⟩ := ihc s M hs z hc hN
        refine ⟨n + 1, (Nat.add_le_add_right hn 1).trans (clock_step (by dsimp [work]; omega) N M), ?_⟩
        simpa only [compile, run, hh] using Block.Exec.branch_true (k := Sum.inl k)
          (a := a.compile) (b := b.compile) hh hrun
  | seq a b iha ihb =>
    obtain ⟨n, hn, ha⟩ := iha s M hs z (hz.mono (le_max_left _ _)) hN
    obtain ⟨m, hm, hb⟩ := ihb (a.run N s) (M + a.work N) (a.run_bounded N s M hs)
      z (hz.mono (le_max_right _ _)) hN
    exact ⟨n + m, (Nat.add_le_add hn hm).trans (clock_add _ _ _ _), Block.Exec.seq ha hb⟩
  | «repeat» a ih =>
    let c := a.depth + 2
    let z' := Function.update z c (z 0)
    have hc : z c = [] := hz.2 a.depth (Nat.lt_succ_self _)
    have hcopy : (Block.copy (.inr 0) (.inr c) (.inr 1)).Exec
        (Sum.elim s z) (Sum.elim s z') (9 * N + 3) := by
      have hh := Block.copy_exec (Sum.inr 0 : K ⊕ ℕ) (.inr c) (.inr 1)
        (by simp [c]) (by simp) (by simp [c]) (Sum.elim s z) hz.1
      simpa only [Sum.elim_inr, hc, List.length_nil, hN, Nat.mul_zero, Nat.zero_add,
        sum_update_right, z'] using hh
    have hz' : Clean a.depth z' := (hz.mono (Nat.le_succ _)).update_above le_rfl _
    have hN' : (z' 0).length = N := by simp [z', c, hN]
    have hend : Function.update z' c [] = z := by
      rw [Function.update_idem, ← hc, Function.update_eq_self]
    have hInv : ∀ i ≤ (z' c).length, Bounded ((a.run N)^[i] s) (M + N * a.work N) := by
      intro i hi
      have hi' : i ≤ N := by simpa only [z', Function.update_self, hN] using hi
      exact (iterate_bounded (a.run N) (a.work N) (a.run_bounded N) s M i hs).mono
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi') _)
    obtain ⟨n, hn, hloop⟩ := counter_loop a.compile (a.run N) a.depth N
      (M + N * a.work N) (clock (a.work N) N (M + N * a.work N))
      (fun s z hz hN hs => ih s _ hs z hz hN) s z' hz' hN' hInv
    simp only [z', c, Function.update_self, hN] at hn hloop
    rw [show Function.update (Function.update z c (z 0)) c [] = z from hend] at hloop
    refine ⟨9 * N + 3 + n, ?_, ?_⟩
    · exact (Nat.add_le_add_left hn _).trans (clock_loop (a.work N) N M)
    · exact Block.Exec.seq hcopy hloop

end Superstring.BitCode.Program

namespace Superstring.BitCode

variable {K : Type} [DecidableEq K]

theorem single_bounded (i : K) (w : List Bool) : Program.Bounded (single i w) w.length := by
  intro j
  by_cases hj : j = i <;> simp [single, hj]

namespace Block

/-- No syntax can modify a register it does not mention. -/
theorem Exec.frame {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (k : K) (hk : k ∉ b.support) : t k = s k := by
  induction h with
  | push i v s => exact Function.update_of_ne (by simpa [support] using hk) _ _
  | pop i s => exact Function.update_of_ne (by simpa [support] using hk) _ _
  | skip => rfl
  | branch_none _ _ ih => exact ih (fun hh => hk (by simp [support, hh]))
  | branch_false _ _ ih => exact ih (fun hh => hk (by simp [support, hh]))
  | branch_true _ _ ih => exact ih (fun hh => hk (by simp [support, hh]))
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ (fun hh => hk (by simp [support, hh]))).trans
      (ih₁ (fun hh => hk (by simp [support, hh])))
  | loop_nil => rfl
  | loop_cons _ _ _ ih₁ ih₂ => exact (ih₂ hk).trans (ih₁ (fun hh => hk (by simp [support, hh])))

/-- The maximum stack length, unlike the total size, needs no finiteness of the
ambient register type. A finite code will subsequently be restricted to its support. -/
theorem Exec.bounded {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (M : ℕ) (hs : Program.Bounded s M) : Program.Bounded t (M + n) := by
  induction h generalizing M with
  | push k v s =>
    exact (hs.mono (Nat.le_add_right M 1)).update k (v :: s k)
      (by simpa only [List.length_cons] using Nat.succ_le_succ (hs k))
  | pop k s =>
    exact (hs.mono (Nat.le_add_right M 1)).update k (s k).tail
      (by simp only [List.length_tail]; have := hs k; omega)
  | skip => exact hs.mono (by omega)
  | branch_none _ _ ih => exact (ih M hs).mono (by omega)
  | branch_false _ _ ih => exact (ih M hs).mono (by omega)
  | branch_true _ _ ih => exact (ih M hs).mono (by omega)
  | seq _ _ ih₁ ih₂ =>
    have hh := ih₂ _ (ih₁ M hs)
    simpa only [Nat.add_assoc] using hh
  | loop_nil => exact hs.mono (by omega)
  | loop_cons _ _ _ ih₁ ih₂ => exact (ih₂ _ (ih₁ M hs)).mono (by omega)

def clearMany : List K → Block K
  | [] => .skip
  | k :: ks => .seq (clear k) (clearMany ks)

def cleared (s : Store K) (l : List K) : Store K := fun k => if k ∈ l then [] else s k

theorem clearMany_exec (l : List K) (s : Store K) (M : ℕ) (hs : Program.Bounded s M) :
    ∃ n ≤ l.length * (2 * M + 1) + 1, (clearMany l).Exec s (cleared s l) n := by
  induction l generalizing s with
  | nil =>
    have he : cleared s [] = s := by funext k; simp [cleared]
    exact ⟨1, by simp, by simpa only [clearMany, he] using Exec.skip s⟩
  | cons k ks ih =>
    obtain ⟨n, hn, hh⟩ := ih (Function.update s k []) (hs.update k [] (by simp))
    have he : cleared (Function.update s k []) ks = cleared s (k :: ks) := by
      funext j
      by_cases hj : j = k <;> by_cases hmem : j ∈ ks <;> simp [cleared, hj, hmem]
    rw [he] at hh
    refine ⟨2 * (s k).length + 1 + n, ?_, Exec.seq (clear_exec k s) hh⟩
    simp only [List.length_cons]
    have := hs k
    nlinarith

/-- Restrict to the finitely many registers used by the actual finite code.
This proves that infinite ambient names are merely notation, not infinite memory
in the delivered machine. Every restricted alphabet is Bool. -/
theorem certificate_any {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (Φ : α → β) (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n ≤ P.eval (ea a).length,
      b.Exec (single i (ea a)) (single o (eb (Φ a))) n) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb Φ, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  classical
  let U := insert i (insert o b.support)
  let R := ↥U
  let i' : R := ⟨i, by simp [U]⟩
  let o' : R := ⟨o, by simp [U]⟩
  let reg : K → R := fun k => if h : k ∈ U then ⟨k, h⟩ else i'
  let code := b.rename reg
  have hreg : ∀ k ∈ b.support, (reg k).val = k := by
    intro k hk
    simp only [reg, dite_eq_left (show k ∈ U by simp [U, hk])]
  have hi (w : List Bool) : single i w ∘ (Subtype.val : R → K) = single i' w := by
    funext j
    have he : j.val = i ↔ j = i' := by
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    simp only [Function.comp_apply, single, he]
  have ho (w : List Bool) : single o w ∘ (Subtype.val : R → K) = single o' w := by
    funext j
    have he : j.val = o ↔ j = o' := by
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    simp only [Function.comp_apply, single, he]
  have hcorrect : ∀ a, ∃ n ≤ P.eval (ea a).length,
      code.Exec (single i' (ea a)) (single o' (eb (Φ a))) n := by
    intro a
    obtain ⟨n, hn, hh⟩ := correct a
    refine ⟨n, hn, ?_⟩
    simpa only [hi, ho] using hh.pullback reg (Subtype.val : R → K) Subtype.val_injective hreg
  exact ⟨code.certificate ea eb Φ i' o' P hcorrect,
    code.certificate_finite ea eb Φ i' o' P hcorrect⟩

/-- Uniformly erase every used non-output stack. A proof of the observed output
and a polynomial clock suffice; hidden garbage is neither permitted nor assumed
away in the exact Mathlib final configuration. -/
theorem certificate_observed {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (Φ : α → β) (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n t, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) t n ∧ t o = eb (Φ a)) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb Φ, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  classical
  let l := ((insert i b.support).erase o).toList
  let code := Block.seq b (clearMany l)
  let Q : Polynomial ℕ := P + Polynomial.C l.length * (2 * (Polynomial.X + P) + 1) + 1
  apply certificate_any ea eb Φ code i o Q
  intro a
  obtain ⟨n, t, hn, hrun, hout⟩ := correct a
  let N := (ea a).length
  have ht := (hrun.bounded N (single_bounded i (ea a))).mono (Nat.add_le_add_left hn N)
  obtain ⟨m, hm, hclear⟩ := clearMany_exec l t (N + P.eval N) ht
  have hfinal : cleared t l = single o (eb (Φ a)) := by
    funext k
    by_cases hko : k = o
    · subst k
      simp [cleared, l, single, hout]
    · by_cases hk : k ∈ l
      · simp [cleared, hk, single, hko]
      · have hnot : k ∉ insert i b.support := by
          intro hh
          apply hk
          simp only [l, Finset.mem_toList, Finset.mem_erase]
          exact ⟨hko, hh⟩
        have hi : k ≠ i := fun he => hnot (by simp [he])
        have hb : k ∉ b.support := fun he => hnot (Finset.mem_insert_of_mem he)
        have htk : t k = [] := by simpa only [single, ite_eq_right hi] using hrun.frame k hb
        simp only [cleared, ite_eq_right hk, single, ite_eq_right hko, htk]
  rw [hfinal] at hclear
  refine ⟨n + m, ?_, Exec.seq hrun hclear⟩
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
  exact (Nat.add_le_add hn hm).trans (by dsimp only [N]; omega)

end Block

end Superstring.BitCode

namespace Superstring.BitCode.Program

variable {K : Type} [DecidableEq K]

/-- A syntactically bounded-loop program gives a polynomial-time
certificate, including finite alphabets and erasure of temporary registers. -/
theorem certificate {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (p : Program K) (i o : K)
    (correct : ∀ a, (p.run (ea a).length (single i (ea a))) o = eb (f a)) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb f, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  let b : Block (K ⊕ ℕ) := .seq (Block.copy (.inl i) (.inr 0) (.inr 1)) p.compile
  let P : Polynomial ℕ := 9 * Polynomial.X + 3 +
    13 * p.polynomial * (Polynomial.X + Polynomial.X + p.polynomial + 1)
  apply Block.certificate_observed ea eb f b (.inl i) (.inl o) P
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
    | inr k =>
      by_cases hk : k = 0 <;> simp [z, single, hk]
  have hcopy := Block.copy_exec (Sum.inl i : K ⊕ ℕ) (.inr 0) (.inr 1)
    Sum.inl_ne_inr Sum.inl_ne_inr (by simp) (single (.inl i) w)
    (by simp [single])
  have hin : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inl i) = w := by simp [single]
  have hout : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) = [] := by simp [single]
  rw [hin, hout] at hcopy
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hcopy
  rw [hinit] at hcopy
  have hz : Clean p.depth z := by
    constructor
    · simp [z, single]
    · intro j _
      simp [z, single]
  have hN : (z 0).length = N := by simp [z, single, N]
  obtain ⟨n, hn, hh⟩ := p.compile_exec N s N (single_bounded i w) z hz hN
  refine ⟨9 * N + 3 + n, Sum.elim (p.run N s) z, ?_, Block.Exec.seq hcopy hh, ?_⟩
  · simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, eval_polynomial]
    exact Nat.add_le_add_left hn (9 * N + 3)
  · exact correct a

end Superstring.BitCode.Program

namespace Superstring.BitCode.Block

variable {K L : Type} [DecidableEq K] [DecidableEq L]

@[simp] theorem update_left (s : Store K) (r : Store L) (k : K) (w : List Bool) :
    Function.update (Sum.elim s r) (.inl k) w = Sum.elim (Function.update s k w) r := by
  funext j
  cases j with
  | inl j => by_cases hj : j = k <;> simp [hj]
  | inr j => simp

@[simp] theorem update_right (s : Store K) (r : Store L) (k : L) (w : List Bool) :
    Function.update (Sum.elim s r) (.inr k) w = Sum.elim s (Function.update r k w) := by
  funext j
  cases j with
  | inl j => simp
  | inr j => by_cases hj : j = k <;> simp [hj]

/-- Renaming into a disjoint register bank preserves a run and frames the
entire other bank, even when that other bank contains nonempty data. -/
theorem Exec.left {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (r : Store L) : (b.rename Sum.inl).Exec (Sum.elim s r) (Sum.elim t r) n := by
  induction h with
  | push k x s =>
    simpa only [rename, Sum.elim_inl, update_left] using Exec.push (.inl k) x (Sum.elim s r)
  | pop k s =>
    simpa only [rename, Sum.elim_inl, update_left] using Exec.pop (.inl k) (Sum.elim s r)
  | skip => exact .skip _
  | branch_none hh _ ih => exact .branch_none hh ih
  | branch_false hh _ ih => exact .branch_false hh ih
  | branch_true hh _ ih => exact .branch_true hh ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | loop_nil hh => exact .loop_nil hh
  | loop_cons hh _ _ ih₁ ih₂ => exact .loop_cons hh ih₁ ih₂

theorem Exec.right {b : Block L} {s t : Store L} {n : ℕ} (h : b.Exec s t n)
    (r : Store K) : (b.rename Sum.inr).Exec (Sum.elim r s) (Sum.elim r t) n := by
  induction h with
  | push k x s =>
    simpa only [rename, Sum.elim_inr, update_right] using Exec.push (.inr k) x (Sum.elim r s)
  | pop k s =>
    simpa only [rename, Sum.elim_inr, update_right] using Exec.pop (.inr k) (Sum.elim r s)
  | skip => exact .skip _
  | branch_none hh _ ih => exact .branch_none hh ih
  | branch_false hh _ ih => exact .branch_false hh ih
  | branch_true hh _ ih => exact .branch_true hh ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | loop_nil hh => exact .loop_nil hh
  | loop_cons hh _ _ ih₁ ih₂ => exact .loop_cons hh ih₁ ih₂

end Superstring.BitCode.Block

end OAI
