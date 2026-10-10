import OAI.Computability.WLIdentification.ExpressionBounds

namespace OAI

namespace WLIdentification

namespace WordExpressions
open ComputationBounds

/-- Uniform polynomial boundedness of a fixed word expression. This is a
proven realizer property, not an oracle or a unit-cost word instruction. -/
def Poly {n : ℕ} (f : (Fin n → Word) → Word) : Prop :=
  ∃ (e : Expr n) (B : ℕ → ℕ), Polynomial B ∧
    (∀ S, e.eval S = f S) ∧
    ∀ S N, (∀ i, (S i).length ≤ N) → e.Bounded S (B N)

namespace Poly

variable {n m : ℕ}

theorem congr {f g : (Fin n → Word) → Word} (h : Poly f) (he : ∀ S, f S = g S) : Poly g := by
  obtain ⟨e,B,hB,heval,hb⟩ := h
  exact ⟨e,B,hB,fun S => (heval S).trans (he S),hb⟩

theorem var (i : Fin n) : Poly (fun S : Fin n → Word => S i) :=
  ⟨.var i, id, identity, fun _ => rfl, fun _ _ h => h i⟩

theorem nil : Poly (fun _ : Fin n → Word => []) :=
  ⟨.nil, fun _ => 0, constant 0, fun _ => rfl, fun _ _ _ => trivial⟩

theorem snoc {f : (Fin n → Word) → Word} (h : Poly f) (b : Bool) : Poly (fun S => f S ++ [b]) := by
  obtain ⟨e,B,hB,he,hb⟩ := h
  refine ⟨.snoc e b, fun N => B N+1, add hB (constant 1), fun S => ?_, ?_⟩
  · simp only [Expr.eval, he]
  · intro S N hS
    try dsimp only
    have hh := hb S N hS
    refine ⟨e.bounded_mono hh (by omega), ?_⟩
    simpa only [List.length_append, List.length_singleton] using
      (Nat.add_le_add_right (e.length_le _ _ hh) 1)

theorem drop {f : (Fin n → Word) → Word} (h : Poly f) : Poly (fun S => (f S).dropLast) := by
  obtain ⟨e,B,hB,he,hb⟩ := h
  exact ⟨.drop e, B,hB,fun S => congrArg List.dropLast (he S),hb⟩

theorem const (w : Word) : Poly (fun _ : Fin n → Word => w) := by
  induction w using List.reverseRecOn with
  | nil => exact nil
  | append_singleton w b ih => exact snoc ih b

theorem cases {f p q r : (Fin n → Word) → Word} (hf : Poly f) (hp : Poly p) (hq : Poly q) (hr : Poly r) :
    Poly (fun S => match (f S).getLast? with
      | none => p S
      | some false => q S
      | some true => r S) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  obtain ⟨a,A,hA,ha,hab⟩ := hp
  obtain ⟨c,C,hC,hc,hcb⟩ := hq
  obtain ⟨d,D,hD,hd,hdb⟩ := hr
  refine ⟨.cases e a c d, fun N => B N+A N+C N+D N, add (add (add hB hA) hC) hD, ?_, ?_⟩
  · intro S
    simp only [Expr.eval, he]
    cases (f S).getLast? with
    | none => exact ha S
    | some b => cases b <;> first | exact hc S | exact hd S
  · intro S N hS
    try dsimp only
    refine ⟨e.bounded_mono (hb S N hS) (by omega), ?_⟩
    cases (e.eval S).getLast? with
    | none => exact a.bounded_mono (hab S N hS) (by omega)
    | some b => cases b with
      | false => exact c.bounded_mono (hcb S N hS) (by omega)
      | true => exact d.bounded_mono (hdb S N hS) (by omega)

theorem rename {f : (Fin n → Word) → Word} (hf : Poly f) (r : Fin n → Fin m) :
    Poly (fun S => f (S ∘ r)) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  exact ⟨e.rename r,B,hB,fun S => (e.eval_rename r S).trans (he _),
    fun S N hS => (e.bounded_rename r S _).mpr (hb _ _ (fun i => hS (r i)))⟩

theorem bind {f : (Fin n → Word) → Word} {g : (Fin (n+1) → Word) → Word}
    (hf : Poly f) (hg : Poly g) : Poly (fun S => g (Fin.snoc S (f S))) := by
  obtain ⟨e,B,hB,he,hb⟩ := hf
  obtain ⟨a,A,hA,ha,hab⟩ := hg
  refine ⟨.bind e a, fun N => B N+A (N+B N), add hB (compose hA (add identity hB)), ?_, ?_⟩
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

theorem subst {f : (Fin n → Word) → Word} {g : Fin n → (Fin m → Word) → Word}
    (hf : Poly f) (hg : ∀ i, Poly (g i)) : Poly (fun S => f (fun i => g i S)) := by
  classical
  obtain ⟨e,B,hB,he,hb⟩ := hf
  choose a A hA ha hab using hg
  let D : ℕ → ℕ := fun N => ∑ i, A i N
  have hfin (s : Finset (Fin n)) : Polynomial (fun N => ∑ i ∈ s, A i N) := by
    induction s using Finset.induction_on with
    | empty => simpa using constant 0
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using add (hA i) ih
  have hD : Polynomial D := hfin Finset.univ
  have hAD (i : Fin n) (N : ℕ) : A i N ≤ D N := by
    exact Finset.single_le_sum (f := fun i => A i N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨e.subst a, fun N => D N+B (D N), add hD (compose hB hD), ?_, ?_⟩
  · intro S
    simp only [Expr.eval_subst, he, ha]
  · intro S N hS
    try dsimp only
    have hs i : (a i).Bounded S (D N) := (a i).bounded_mono (hab i S N hS) (hAD i N)
    apply e.bounded_subst a S _ (fun i => (a i).bounded_mono (hs i) (by omega))
    exact e.bounded_mono (hb _ (D N) (fun i => (a i).length_le _ _ (hs i))) (by omega)

theorem stages_congr {f g : (Fin (n+2) → Word) → Word} (h : ∀ S, f S = g S)
    (S : Fin n → Word) (a : Word) (k : ℕ) : Expr.stages f S a k = Expr.stages g S a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Expr.stages, h, ih]

/-- Polynomial bounded loop rule. The index and accumulator bounds are
mathematical invariants of the actual semantics; no execution primitive is added. -/
theorem loop {c a : (Fin n → Word) → Word} {f : (Fin (n+2) → Word) → Word}
    (hc : Poly c) (ha : Poly a) (hf : Poly f) (H : ℕ → ℕ) (hH : Polynomial H)
    (hstage : ∀ S N, (∀ j, (S j).length ≤ N) → ∀ i ≤ (c S).length,
      (Expr.stages f S (a S) i).length ≤ H N) :
    Poly (fun S => Expr.stages f S (a S) (c S).length) := by
  obtain ⟨ce,C,hC,hce,hcb⟩ := hc
  obtain ⟨ae,A,hA,hae,hab⟩ := ha
  obtain ⟨fe,F,hF,hfe,hfb⟩ := hf
  let D := fun N => C N+A N+F (N+C N+H N)
  have hp : Polynomial D := add (add hC hA) (compose hF (add (add identity hC) hH))
  refine ⟨.loop ce ae fe, D,hp,?_,?_⟩
  · intro S
    simp only [Expr.eval, hce, hae]
    exact stages_congr hfe _ _ _
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
    · simp only [Fin.snoc_last, hae, stages_congr hfe]
      have hi' : i ≤ (c S).length := by rw [← hce]; omega
      exact (hstage S N hS i hi').trans (by omega)
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.snoc_last, List.length_replicate]
        have := ce.length_le _ _ hcS
        omega
      · simpa only [Fin.snoc_castSucc] using (hS k).trans (by omega : N ≤ N+C N+H N)

end Poly
end WordExpressions

namespace WordExpressions

abbrev unary (n : ℕ) : Word := List.replicate n false
abbrev boolWord (b : Bool) : Word := [b]

def old {n : ℕ} (i : Fin n) : Fin (n+2) := i.castSucc.castSucc
def index (n : ℕ) : Fin (n+2) := (Fin.last n).castSucc
def accum (n : ℕ) : Fin (n+2) := Fin.last (n+1)

@[simp] theorem extend_old {n} (S : Fin n → Word) (u v : Word) (i : Fin n) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) (old i) = S i := by simp [old]
@[simp] theorem extend_index {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) (index n) = u := by simp [index]
@[simp] theorem extend_accum {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) (accum n) = v := by simp [accum]

@[simp] theorem snoc_prefix {n} (S : Fin n → Word) (u : Word) :
    (Fin.snoc S u : Fin (n+1) → Word) ∘ Fin.castSucc = S := by
  funext i; simp
@[simp] theorem extend_prefix {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) ∘ Fin.castSucc = Fin.snoc S u := by
  funext i; simp
@[simp] theorem extend_base {n} (S : Fin n → Word) (u v : Word) :
    (Fin.snoc (Fin.snoc S u) v : Fin (n+2) → Word) ∘ old = S := by
  funext i; simp

namespace Poly
variable {n : ℕ}

theorem branches {p : (Fin n → Word) → Bool} {f g : (Fin n → Word) → Word}
    (hp : Poly (fun S => boolWord (p S))) (hf : Poly f) (hg : Poly g) :
    Poly (fun S => if p S then f S else g S) := by
  apply (cases hp hg hg hf).congr
  intro S
  cases p S <;> rfl

theorem emptyTest {f : (Fin n → Word) → Word} (hf : Poly f) :
    Poly (fun S => boolWord (decide (f S = []))) := by
  apply (cases hf (const [true]) (const [false]) (const [false])).congr
  intro S
  cases he : (f S).getLast? with
  | none =>
    have hz : f S = [] := List.getLast?_eq_none_iff.mp he
    simp [hz, boolWord]
  | some b =>
    have hz : f S ≠ [] := by intro h; simp [h] at he
    cases b <;> simp [hz, boolWord]

theorem length (i : Fin n) : Poly (fun S : Fin n → Word => unary (S i).length) := by
  let body : (Fin (n+2) → Word) → Word := fun T => T (accum n) ++ [false]
  have hb : Poly body := snoc (var _) false
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages body S [] k = unary k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Expr.stages, body, extend_accum, ih, unary, List.replicate_succ']
  obtain h := loop (var i) nil hb id ComputationBounds.identity (by
    intro S N hS k hk
    rw [hs]
    simpa using hk.trans (hS i))
  exact h.congr (fun S => hs S _)

theorem unaryLength {f : (Fin n → Word) → Word} (hf : Poly f) :
    Poly (fun S => unary (f S).length) := by
  have h := (length (0 : Fin 1)).subst (g := fun _ => f) (fun _ => hf)
  exact h.congr (fun _ => rfl)

theorem stages_drop {n} (S : Fin n → Word) (w : Word) (k : ℕ) :
    Expr.stages (fun T => (T (accum n)).dropLast) S w k = w.take (w.length-k) := by
  induction k with
  | zero => simp [Expr.stages]
  | succ k ih =>
    simp only [Expr.stages, extend_accum]
    rw [ih]
    simp only [List.dropLast_eq_take, List.length_take, List.take_take]
    congr 1
    omega

theorem cut (i j : Fin n) : Poly (fun S : Fin n → Word => (S i).take ((S i).length-(S j).length)) := by
  have hstep : Poly (fun T : Fin (n+2) → Word => (T (accum n)).dropLast) := drop (var _)
  have h := loop (var j) (var i) hstep id ComputationBounds.identity (by
    intro S N hS k _
    rw [stages_drop]
    simp only [List.length_take]
    exact (min_le_right _ _).trans (hS i))
  exact h.congr (fun S => stages_drop S _ _)

theorem cutOf {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => (f S).take ((f S).length-(g S).length)) := by
  have h := (cut (0 : Fin 2) 1).subst (g := ![f,g]) (by intro i; fin_cases i; exacts [hf,hg])
  exact h.congr (fun _ => rfl)

theorem sub {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => unary ((f S).length-(g S).length)) := by
  apply (cutOf (unaryLength hf) hg).congr
  intro S
  simp [unary, List.take_replicate]

theorem le {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => boolWord (decide ((f S).length ≤ (g S).length))) := by
  apply (emptyTest (sub hf hg)).congr
  intro S
  simp [unary, Nat.sub_eq_zero_iff_le]

theorem stages_add {n} (S : Fin n → Word) (a k : ℕ) :
    Expr.stages (fun T => T (accum n) ++ [false]) S (unary a) k = unary (a+k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Expr.stages, extend_accum, ih, unary]
    rw [← Nat.add_assoc, List.replicate_succ']

theorem add (i j : Fin n) : Poly (fun S : Fin n → Word => unary ((S i).length+(S j).length)) := by
  have h := loop (var j) (length i) (snoc (var (accum n)) false)
    (fun N => N+N) (ComputationBounds.add ComputationBounds.identity ComputationBounds.identity) (by
      intro S N hS k hk
      rw [stages_add]
      simp only [unary, List.length_replicate]
      exact Nat.add_le_add (hS i) (hk.trans (hS j)))
  exact h.congr (fun S => stages_add S _ _)

theorem addOf {f g : (Fin n → Word) → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun S => unary ((f S).length+(g S).length)) := by
  have h := (add (0 : Fin 2) 1).subst (g := ![f,g]) (by intro i; fin_cases i; exacts [hf,hg])
  exact h.congr (fun _ => rfl)

end Poly
end WordExpressions

end WLIdentification

end OAI
