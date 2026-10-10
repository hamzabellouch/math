import OAI.Computability.WLIdentification.PolynomialArithmetic

namespace OAI

namespace WLIdentification

namespace NumericFinite

def elements (b : ℕ) (p : ℕ → Bool) : List ℕ := (List.range b).filter p
def count (b : ℕ) (p : ℕ → Bool) : ℕ := (elements b p).length

@[simp] theorem elements_zero (p : ℕ → Bool) : elements 0 p = [] := rfl
@[simp] theorem elements_succ (b : ℕ) (p : ℕ → Bool) :
    elements (b+1) p = elements b p ++ if p b then [b] else [] := by
  simp only [elements, List.range_succ, List.filter_append]
  cases hb : p b <;> simp [hb]

@[simp] theorem count_zero (p : ℕ → Bool) : count 0 p = 0 := rfl
@[simp] theorem count_succ (b : ℕ) (p : ℕ → Bool) :
    count (b+1) p = count b p + if p b then 1 else 0 := by
  simp only [count, elements_succ, List.length_append]
  cases p b <;> rfl

theorem mem_elements {b v : ℕ} {p : ℕ → Bool} : v ∈ elements b p ↔ v < b ∧ p v = true := by
  simp [elements, and_comm]

theorem count_mono (p : ℕ → Bool) {a b : ℕ} (h : a ≤ b) : count a p ≤ count b p := by
  induction h with
  | refl => rfl
  | @step b h ih => rw [count_succ]; omega

theorem count_strict {p : ℕ → Bool} {a b : ℕ} (h : a < b) (ha : p a = true) :
    count a p < count b p := by
  have hh := count_mono p h
  rw [count_succ, ha] at hh
  simp only [↓reduceIte] at hh
  omega

theorem rank (b : ℕ) (p : ℕ → Bool) (j : ℕ) (hj : j < (elements b p).length) :
    count (elements b p)[j] p = j := by
  induction b with
  | zero => simp at hj
  | succ b ih =>
    by_cases hp : p b = true
    · have he : elements (b+1) p = elements b p ++ [b] := by simp [hp]
      simp only [he, List.length_append, List.length_singleton] at hj
      simp only [he]
      by_cases hh : j < (elements b p).length
      · rw [List.getElem_append_left hh]
        exact ih hh
      · have hj' : j = (elements b p).length := by omega
        subst j
        simp [count]
    · have he : elements (b+1) p = elements b p := by simp [hp]
      simp only [he]
      exact ih (by simpa only [he] using hj)

def select (b : ℕ) (p : ℕ → Bool) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun i => i < b ∧ p i = true ∧ count i p = j) b

theorem select_correct (b : ℕ) (p : ℕ → Bool) (j : ℕ) (hj : j < (elements b p).length) :
    select b p j = (elements b p)[j] := by
  let v := (elements b p)[j]
  have hv : v < b ∧ p v = true := mem_elements.mp (List.getElem_mem hj)
  have hr : count v p = j := rank b p j hj
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨by omega, fun _ => ⟨hv.1,hv.2,hr⟩, ?_⟩
  intro i hi _ hh
  have hlt := count_strict (p := p) hi hv.2
  exact (ne_of_gt hlt) (hh.2.2.trans hr.symm)

end NumericFinite
namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem filterCount {b : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hb : NatPoly b) (hp : BoolPoly p) :
    NatPoly (fun S => NumericFinite.count (b S) (fun i => p (Fin.snoc S (unary i)))) := by
  apply (sum hb (ite hp (const 1) (const 0))).congr
  intro S
  dsimp only
  congr 1
  generalize b S = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.sum_range_succ, ih, NumericFinite.count_succ]

end WordExpressions.NatPoly
namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem filterSelect {b j : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hb : NatPoly b) (hj : NatPoly j) (hp : BoolPoly p) :
    NatPoly (fun S => NumericFinite.select (b S) (fun i => p (Fin.snoc S (unary i))) (j S)) := by
  have hp' : BoolPoly (fun T : Fin (n+2) → Word =>
      p (Fin.snoc (T ∘ Fin.castSucc ∘ Fin.castSucc) (T (Fin.last (n+1))))) :=
    Poly.applyWord hp (Fin.castSucc ∘ Fin.castSucc) (Poly.var _)
  have hc := filterCount (var (Fin.last n)) hp'
  have htest := BoolPoly.and (lt (var (Fin.last n)) (rename hb Fin.castSucc))
    (BoolPoly.and hp (eqtest hc (rename hj Fin.castSucc)))
  apply (findGreatest hb htest).congr
  intro S
  dsimp only [NumericFinite.select]
  congr 2
  funext i
  simp only [Fin.snoc_last, unary, List.length_replicate, snoc_prefix,
    Bool.and_eq_true, decide_eq_true_eq]
  simp only [Function.comp_def, Fin.snoc_castSucc]

end WordExpressions.NatPoly

namespace WordExpressions.Expr
open StackModel.Command ComputationBounds

def decisionBound {n} (e : Expr n) (B : ℕ) : ℕ :=
  2+(e.cost B+15*B+15)*(2*(B+(e.cost B+15*B+15))+3)

theorem decisionBound_polynomial {n} (e : Expr n) : Polynomial e.decisionBound := by
  have h := add (add e.cost_polynomial (mul (constant 15) identity)) (constant 15)
  exact add (constant 2) (mul h (add (mul (constant 2) (add identity h)) (constant 3)))

/-- The output bit is tested by three actual finite-control instructions.
Rejection is a literal rejecting state, including on malformed words. -/
theorem decides (e : Expr 1) (B : ℕ → ℕ)
    (hw : ∀ n, n ≤ B n) (h : ∀ w, e.Bounded (fun _ => w) (B w.length)) :
    ∃ M : Machine, DecidesWithin M {w | (e.eval (fun _ => w)).getLast?.getD false = true}
      (fun n => e.decisionBound (B n)) := by
  obtain ⟨N,hN,hsmall⟩ := e.outputCode.small_exists
  let c := e.outputCode.rename (finiteIndex N (by omega))
  let input : Fin N := finiteIndex N (by omega) 0
  let P := c.testProgram none input
  refine ⟨StackModel.compile P input, ?_⟩
  intro w
  obtain ⟨t,ht,he⟩ := e.outputCode_exec w (B w.length) (hw _) (h w)
  have he' := he.restrict N (by omega) hsmall
  simp only [restrict_update (show 0 < N by omega) (show 0 < N by omega)] at he'
  have hs : (fun _ : ℕ => ([] : Word)) ∘ Fin.val = fun _ : Fin N => [] := rfl
  rw [hs] at he'
  have hr := he'.testRun input input w rfl
  simp only [input, Function.update_self] at hr
  change (StackModel.run P input w (3+t)).control =
    .inl ((e.eval (fun _ => w)).getLast?.getD false) at hr
  obtain ⟨T,hT,hTe⟩ := StackModel.run_execution P input w (3+t)
  refine ⟨T, ?_, ?_, ?_⟩
  · apply hT.trans
    dsimp only [decisionBound]
    have htp : 3+t ≤ e.cost (B w.length)+15*(B w.length)+15 := by omega
    have hn := hw w.length
    gcongr
  · rw [hTe]
    simp only [Halted, StackModel.encodeConfig, hr]
    cases hb : (e.eval (fun _ => w)).getLast?.getD false <;> simp
  · rw [hTe]
    simp only [StackModel.encodeConfig, hr, Set.mem_ofPred_eq]
    cases hb : (e.eval (fun _ => w)).getLast?.getD false <;> simp
    change ¬(2 : Fin ((StackModel.compile P input).extraStates+3)) = 1
    intro heq
    have hv := congrArg Fin.val heq
    change 2 % ((StackModel.compile P input).extraStates+3) =
      1 % ((StackModel.compile P input).extraStates+3) at hv
    have h1 : 1 < (StackModel.compile P input).extraStates+3 := by omega
    have h2 : 2 < (StackModel.compile P input).extraStates+3 := by omega
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1] at hv
    omega

end WordExpressions.Expr
namespace ComputationBounds

/-- A single exponential with a polynomial exponent (not an iterated exponential). -/
def Exponential (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ 2^(C*(n+1)^d)

theorem power {f : ℕ → ℕ} (hf : Polynomial f) (d : ℕ) : Polynomial (fun n => (f n)^d) := by
  induction d with
  | zero => simpa using constant 1
  | succ d ih => simpa only [pow_succ] using mul ih hf

theorem exp_dominates {f g : ℕ → ℕ} (hf : Exponential f) (h : ∀ n, g n ≤ f n) : Exponential g := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun n => (h n).trans (hf n)⟩

theorem two_pow {f : ℕ → ℕ} (hf : Polynomial f) : Exponential (fun n => 2^(f n)) := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun n => Nat.pow_le_pow_right (by decide) (hf n)⟩

theorem polynomial_exponential {f : ℕ → ℕ} (hf : Polynomial f) : Exponential f :=
  exp_dominates (two_pow hf) (fun _ => (Nat.lt_two_pow_self).le)

theorem exp_constant (c : ℕ) : Exponential (fun _ => c) := polynomial_exponential (constant c)

theorem exp_identity : Exponential id := polynomial_exponential identity

theorem exp_add {f g : ℕ → ℕ} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n+g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  let p := fun n => C*(n+1)^d
  let q := fun n => D*(n+1)^e
  have hp : Polynomial p := ⟨C,d,fun _ => le_rfl⟩
  have hq : Polynomial q := ⟨D,e,fun _ => le_rfl⟩
  apply exp_dominates (two_pow (add (add hp hq) (constant 1)))
  intro n
  have ha : f n ≤ 2^(p n+q n) := (hf n).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right (p n) (q n)))
  have hb : g n ≤ 2^(p n+q n) := (hg n).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left (q n) (p n)))
  change f n+g n ≤ 2^(p n+q n+1)
  rw [pow_succ]
  omega

theorem exp_mul {f g : ℕ → ℕ} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n*g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  have hp : Polynomial (fun n => C*(n+1)^d) := ⟨C,d,fun _ => le_rfl⟩
  have hq : Polynomial (fun n => D*(n+1)^e) := ⟨D,e,fun _ => le_rfl⟩
  apply exp_dominates (two_pow (add hp hq))
  intro n
  simpa only [pow_add] using Nat.mul_le_mul (hf n) (hg n)

theorem exp_power {f : ℕ → ℕ} (hf : Exponential f) (d : ℕ) : Exponential (fun n => (f n)^d) := by
  induction d with
  | zero => simpa using exp_constant 1
  | succ d ih => simpa only [pow_succ] using exp_mul ih hf

theorem polynomial_exp_comp {f g : ℕ → ℕ} (hf : Polynomial f) (hg : Exponential g) :
    Exponential (fun n => f (g n)) := by
  obtain ⟨C,d,hf⟩ := hf
  exact exp_dominates (exp_mul (exp_constant C) (exp_power (exp_add hg (exp_constant 1)) d))
    (fun n => hf (g n))

end ComputationBounds

end WLIdentification

end OAI
