import OAI.Computability.WLIdentification.FiniteEncoding

namespace OAI

namespace WLIdentification

namespace WordExpressions
open ComputationBounds

/-- One-exponential realizability by a single finite word expression, with
an explicit bound on all its intermediate words. -/
def Exp {n : ℕ} (f : (Fin n → Word) → Word) : Prop :=
  ∃ (e : Expr n) (B : ℕ → ℕ), Exponential B ∧
    (∀ S, e.eval S = f S) ∧
    ∀ S N, (∀ i, (S i).length ≤ N) → e.Bounded S (B N)

theorem Poly.toExp {n} {f : (Fin n → Word) → Word} (hf : Poly f) : Exp f := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  exact ⟨e,B,polynomial_exponential hB,he,hb⟩

namespace Exp
variable {n : ℕ}

theorem congr {f g : (Fin n → Word) → Word} (h : Exp f) (he : ∀ S, f S = g S) : Exp g := by
  obtain ⟨e,B,hB,heval,hb⟩ := h
  exact ⟨e,B,hB,fun S => (heval S).trans (he S),hb⟩

/-- Feeding one-exponential data to a fixed polynomial word program stays
single-exponential; arbitrary composition of two exponential programs is not asserted. -/
theorem bindPoly {f : (Fin n → Word) → Word} {g : (Fin (n+1) → Word) → Word}
    (hf : Exp f) (hg : Poly g) : Exp (fun S => g (Fin.snoc S (f S))) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  obtain ⟨a,A,hA,ha,hab⟩ := hg
  refine ⟨.bind e a, fun N => B N+A (N+B N),
    exp_add hB (polynomial_exp_comp hA (exp_add exp_identity hB)), ?_, ?_⟩
  · intro S
    simp only [Expr.eval, ha, he]
  · intro S N hS
    try dsimp only
    have hs := hb S N hS
    refine ⟨e.bounded_mono hs (by omega), ?_⟩
    apply a.bounded_mono (hab _ (N+B N) ?_) (by omega)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (e.length_le _ _ hs).trans (by omega : B N ≤ N+B N)
    · simpa only [Fin.snoc_castSucc] using (hS j).trans (by omega : N ≤ N+B N)

theorem loopPoly {c a : (Fin n → Word) → Word} {f : (Fin (n+2) → Word) → Word}
    (hc : Poly c) (ha : Poly a) (hf : Poly f) (H : ℕ → ℕ) (hH : Exponential H)
    (hstage : ∀ S N, (∀ j, (S j).length ≤ N) → ∀ i ≤ (c S).length,
      (Expr.stages f S (a S) i).length ≤ H N) :
    Exp (fun S => Expr.stages f S (a S) (c S).length) := by
  obtain ⟨ce,C,hC,hce,hcb⟩ := hc
  obtain ⟨ae,A,hA,hae,hab⟩ := ha
  obtain ⟨fe,F,hF,hfe,hfb⟩ := hf
  let D := fun N => C N+A N+F (N+C N+H N)
  have hp : Exponential D := exp_add (polynomial_exponential (add hC hA))
    (polynomial_exp_comp hF (exp_add (polynomial_exponential (add identity hC)) hH))
  refine ⟨.loop ce ae fe, D,hp,?_,?_⟩
  · intro S
    simp only [Expr.eval, hce, hae]
    exact Poly.stages_congr hfe _ _ _
  · intro S N hS
    try dsimp only
    have hcS := hcb S N hS
    have haS := hab S N hS
    refine ⟨ce.bounded_mono hcS (by dsimp [D]; omega),
      ae.bounded_mono haS (by dsimp [D]; omega), ?_⟩
    intro i hi
    apply fe.bounded_mono (hfb _ (N+C N+H N) ?_) (by dsimp [D]; omega)
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, hae, Poly.stages_congr hfe]
      have hi' : i ≤ (c S).length := by rw [← hce]; omega
      exact (hstage S N hS i hi').trans (by omega)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.snoc_last, List.length_replicate]
        have := ce.length_le _ _ hcS
        omega
      · simpa only [Fin.snoc_castSucc] using (hS k).trans (by omega : N ≤ N+C N+H N)

theorem powerBudget (C d : ℕ) :
    Exp (fun S : Fin 1 → Word => unary (2^(C*((S 0).length+1)^d))) := by
  have hp : NatPoly (fun S : Fin 1 → Word => C*((S 0).length+1)^d) :=
    NatPoly.mul (NatPoly.const C) (NatPoly.pow_const (NatPoly.succ (NatPoly.var 0)) d)
  let f : (Fin 3 → Word) → Word := fun T => T (accum 1) ++ T (accum 1)
  have hf : Poly f := Poly.append (Poly.var _) (Poly.var _)
  have hs (S : Fin 1 → Word) (i : ℕ) : Expr.stages f S (unary 1) i = unary (2^i) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [Expr.stages, f, extend_accum, ih, unary]
      rw [← List.replicate_add, pow_succ]
      congr 1
      omega
  have h := loopPoly hp (Poly.const (unary 1)) hf (fun N => 2^(C*(N+1)^d))
    ⟨C,d,fun _ => le_rfl⟩ (by
      intro S N hS i hi
      rw [hs]
      simp only [unary, List.length_replicate] at hi ⊢
      apply Nat.pow_le_pow_right (by decide)
      exact hi.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by have := hS 0; omega) d)))
  apply h.congr
  intro S
  simpa only [unary, List.length_replicate] using hs S (C*((S 0).length+1)^d)

/-- A genuine EXPTIME decider from a proved single-exponential Boolean program. -/
theorem inEXPTIME {p : (Fin 1 → Word) → Bool} (hp : Exp (fun S => boolWord (p S))) :
    InEXPTIME {w | p (fun _ => w) = true} := by
  obtain ⟨e,B,hB,he,hbound⟩ := hp
  let D := fun n => n+B n
  have hd : ∀ n, n ≤ D n := fun n => Nat.le_add_right _ _
  have hb : ∀ w, e.Bounded (fun _ => w) (D w.length) := by
    intro w
    exact e.bounded_mono (hbound _ _ (by intro i; rfl)) (Nat.le_add_left _ _)
  obtain ⟨M,hM⟩ := e.decides D hd hb
  obtain ⟨C,d,hCd⟩ := polynomial_exp_comp e.decisionBound_polynomial (exp_add exp_identity hB)
  refine ⟨M,C,d,?_⟩
  intro w
  obtain ⟨t,ht,hhalt,hacc⟩ := hM w
  refine ⟨t,ht.trans (hCd w.length),hhalt,?_⟩
  simpa only [Set.mem_ofPred_eq, he, boolWord, List.getLast?_singleton, Option.getD_some] using hacc

end Exp

/-- A polynomial budget-relative test is executed on a physically generated
unary exponential budget, rather than receiving an oracle-size bound. -/
theorem inEXPTIME_of_budget {L : BinaryLanguage} (C d : ℕ)
    {p : (Fin 2 → Word) → Bool} (hp : BoolPoly p)
    (h : ∀ w, p ![w, unary (2^(C*(w.length+1)^d))] = true ↔ w ∈ L) : InEXPTIME L := by
  have he := Exp.bindPoly (Exp.powerBudget C d) hp
  have hE := Exp.inEXPTIME he
  have hset : {w | p (Fin.snoc (fun _ : Fin 1 => w) (unary (2^(C*(w.length+1)^d)))) = true} = L := by
    ext w
    have henv : Fin.snoc (fun _ : Fin 1 => w) (unary (2^(C*(w.length+1)^d))) =
        ![w, unary (2^(C*(w.length+1)^d))] := by
      funext i
      fin_cases i <;> rfl
    simpa only [Set.mem_ofPred_eq, henv] using h w
  simpa only [hset] using hE

end WordExpressions

namespace WordExpressions
namespace BoolPoly
variable {n : ℕ}

theorem allRange {b : (Fin n → Word) → ℕ} {p : (Fin n → Word) → ℕ → Bool}
    (hb : NatPoly b)
    (hp : BoolPoly (fun T => p (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    BoolPoly (fun S => (List.range (b S)).all (p S)) := by
  apply (boundedAll hb hp).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

theorem anyRange {b : (Fin n → Word) → ℕ} {p : (Fin n → Word) → ℕ → Bool}
    (hb : NatPoly b)
    (hp : BoolPoly (fun T => p (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    BoolPoly (fun S => (List.range (b S)).any (p S)) := by
  apply (boundedAny hb hp).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

end BoolPoly
namespace NatPoly
variable {n : ℕ}

theorem sumRange {b : (Fin n → Word) → ℕ} {f : (Fin n → Word) → ℕ → ℕ}
    (hb : NatPoly b)
    (hf : NatPoly (fun T => f (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    NatPoly (fun S => ((List.range (b S)).map (f S)).sum) := by
  apply (sum hb hf).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

end NatPoly
namespace Poly
variable {n : ℕ}

theorem tabulateRange {b : (Fin n → Word) → ℕ} {p : (Fin n → Word) → ℕ → Bool}
    (hb : NatPoly b)
    (hp : BoolPoly (fun T => p (T ∘ Fin.castSucc) ((T (Fin.last n)).length))) :
    Poly (fun S => (List.range (b S)).map (p S)) := by
  apply (tabulate hb hp).congr
  intro S
  simp only [snoc_prefix, Fin.snoc_last, unary, List.length_replicate]

end Poly
end WordExpressions

/-- Proof-generating syntactic closure for fixed word arithmetic.  Each leaf is
an already proved finite-word implementation, not an evaluation oracle. -/
macro "word_poly" : tactic => `(tactic|
  repeat' first
  | exact WordExpressions.Poly.var _
  | exact WordExpressions.NatPoly.var _
  | exact WordExpressions.NatPoly.const _
  | exact WordExpressions.BoolPoly.const _
  | exact WordExpressions.Poly.const _
  | apply WordExpressions.NatPoly.add
  | apply WordExpressions.NatPoly.mul
  | apply WordExpressions.NatPoly.sub
  | apply WordExpressions.NatPoly.succ
  | apply WordExpressions.NatPoly.div
  | apply WordExpressions.NatPoly.mod
  | apply WordExpressions.NatPoly.cappedPow
  | apply WordExpressions.NatPoly.min
  | apply WordExpressions.NatPoly.max
  | apply WordExpressions.NatPoly.pair
  | apply WordExpressions.NatPoly.unpair_fst
  | apply WordExpressions.NatPoly.unpair_snd
  | apply WordExpressions.NatPoly.decode
  | apply WordExpressions.NatPoly.ite
  | apply WordExpressions.NatPoly.length
  | apply WordExpressions.BoolPoly.and
  | apply WordExpressions.BoolPoly.or
  | apply WordExpressions.BoolPoly.not
  | apply WordExpressions.NatPoly.eqtest
  | apply WordExpressions.NatPoly.lt
  | apply WordExpressions.NatPoly.le
  | apply WordExpressions.Poly.nth
  | apply WordExpressions.BoolPoly.allRange
  | apply WordExpressions.BoolPoly.anyRange
  | apply WordExpressions.NatPoly.sumRange
  | apply WordExpressions.Poly.tabulateRange
  )

namespace WordExpressions
namespace NatPoly
variable {n : ℕ}
theorem iteProp {p : (Fin n → Word) → Prop} [∀ S, Decidable (p S)]
    {f g : (Fin n → Word) → ℕ} (hp : BoolPoly (fun S => decide (p S)))
    (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => if p S then f S else g S) := by
  simpa only [decide_eq_true_eq] using ite hp hf hg
end NatPoly
namespace BoolPoly
variable {n : ℕ}
theorem ite {p f g : (Fin n → Word) → Bool} (hp : BoolPoly p) (hf : BoolPoly f) (hg : BoolPoly g) :
    BoolPoly (fun S => if p S then f S else g S) := by
  apply (Poly.branches hp hf hg).congr
  intro S
  dsimp only
  cases p S <;> rfl
theorem iteProp {p : (Fin n → Word) → Prop} [∀ S, Decidable (p S)]
    {f g : (Fin n → Word) → Bool} (hp : BoolPoly (fun S => decide (p S)))
    (hf : BoolPoly f) (hg : BoolPoly g) : BoolPoly (fun S => if p S then f S else g S) := by
  simpa only [decide_eq_true_eq] using ite hp hf hg
end BoolPoly
end WordExpressions

end WLIdentification

end OAI
