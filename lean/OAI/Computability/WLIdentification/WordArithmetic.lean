import OAI.Computability.WLIdentification.PolynomialWords

namespace OAI

namespace WLIdentification

namespace WordExpressions
abbrev NatPoly {n} (f : (Fin n → Word) → ℕ) : Prop := Poly (fun S => unary (f S))
abbrev BoolPoly {n} (p : (Fin n → Word) → Bool) : Prop := Poly (fun S => boolWord (p S))

namespace BoolPoly
variable {n : ℕ}
theorem const (b : Bool) : BoolPoly (fun _ : Fin n → Word => b) := Poly.const [b]
theorem not {p : (Fin n → Word) → Bool} (hp : BoolPoly p) : BoolPoly (fun S => !(p S)) := by
  apply (Poly.branches hp (const false) (const true)).congr
  intro S; dsimp only; cases p S <;> rfl
theorem and {p q : (Fin n → Word) → Bool} (hp : BoolPoly p) (hq : BoolPoly q) :
    BoolPoly (fun S => p S && q S) := by
  apply (Poly.branches hp hq (const false)).congr
  intro S; dsimp only; cases p S <;> rfl
theorem or {p q : (Fin n → Word) → Bool} (hp : BoolPoly p) (hq : BoolPoly q) :
    BoolPoly (fun S => p S || q S) := by
  apply (Poly.branches hp (const true) hq).congr
  intro S; dsimp only; cases p S <;> rfl
theorem rename {p : (Fin n → Word) → Bool} (hp : BoolPoly p) {m} (r : Fin n → Fin m) :
    BoolPoly (fun S => p (S ∘ r)) := Poly.rename hp r
end BoolPoly

namespace NatPoly
variable {n : ℕ}
theorem length {f : (Fin n → Word) → Word} (hf : Poly f) : NatPoly (fun S => (f S).length) :=
  Poly.unaryLength hf
theorem var (i : Fin n) : NatPoly (fun S : Fin n → Word => (S i).length) := Poly.length i
theorem const (c : ℕ) : NatPoly (fun _ : Fin n → Word => c) := Poly.const (unary c)
theorem rename {f : (Fin n → Word) → ℕ} (hf : NatPoly f) {m} (r : Fin n → Fin m) :
    NatPoly (fun S => f (S ∘ r)) := Poly.rename hf r

theorem add {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => f S+g S) := by
  apply (Poly.addOf hf hg).congr
  intro S; simp [unary]
theorem succ {f : (Fin n → Word) → ℕ} (hf : NatPoly f) : NatPoly (fun S => f S+1) := add hf (const 1)
theorem sub {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => f S-g S) := by
  apply (Poly.sub hf hg).congr
  intro S; simp [unary]
theorem le {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    BoolPoly (fun S => decide (f S ≤ g S)) := by
  apply (Poly.le hf hg).congr
  intro S; simp [unary]
theorem lt {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    BoolPoly (fun S => decide (f S < g S)) := by
  apply (le (succ hf) hg).congr
  intro S; simp
theorem eqtest {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    BoolPoly (fun S => decide (f S = g S)) := by
  apply (BoolPoly.and (le hf hg) (le hg hf)).congr
  intro S; simp [boolWord, Nat.le_antisymm_iff]
theorem ite {p : (Fin n → Word) → Bool} {f g : (Fin n → Word) → ℕ}
    (hp : BoolPoly p) (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => if p S then f S else g S) := by
  apply (Poly.branches hp hf hg).congr
  intro S; dsimp only; cases p S <;> rfl

theorem max {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => max (f S) (g S)) := by
  apply (ite (le hf hg) hg hf).congr
  intro S; by_cases h : f S ≤ g S <;> simp [h, max_def]
theorem min {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => min (f S) (g S)) := by
  apply (ite (le hf hg) hf hg).congr
  intro S; by_cases h : f S ≤ g S <;> simp [h, min_def]

theorem mulVars (i j : Fin n) : NatPoly (fun S : Fin n → Word => (S i).length*(S j).length) := by
  let step : (Fin (n+2) → Word) → Word := fun T => unary ((T (accum n)).length+(T (old i)).length)
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages step S [] k = unary ((S i).length*k) := by
    induction k with
    | zero => simp [Expr.stages, unary]
    | succ k ih => simp [Expr.stages, step, ih, unary, Nat.mul_succ]
  have h := Poly.loop (Poly.var j) Poly.nil (Poly.add (accum n) (old i))
    (fun N => N*N) (ComputationBounds.mul ComputationBounds.identity ComputationBounds.identity) (by
      intro S N hS k hk
      change (Expr.stages step S [] k).length ≤ _
      rw [hs]
      simpa only [unary, List.length_replicate] using Nat.mul_le_mul (hS i) (hk.trans (hS j)))
  exact h.congr (fun S => hs S _)

theorem mul {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun S => f S*g S) := by
  have h := (mulVars (0 : Fin 2) 1).subst (g := ![(fun S => unary (f S)),(fun S => unary (g S))])
    (by intro i; fin_cases i; exacts [hf,hg])
  apply h.congr
  intro S; simp [unary]

theorem pow_const {f : (Fin n → Word) → ℕ} (hf : NatPoly f) (d : ℕ) : NatPoly (fun S => (f S)^d) := by
  induction d with
  | zero => simpa using const 1
  | succ d ih => simpa only [pow_succ] using mul ih hf

end NatPoly

namespace Poly
variable {n : ℕ}

/-- The i-th bit in left-to-right order, with a false default outside the word. -/
theorem nth {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : BoolPoly (fun S => (w S)[i S]?.getD false) := by
  let amount := fun S => (w S).length-(i S+1)
  have hamt : NatPoly amount := NatPoly.sub (NatPoly.length hw) (NatPoly.succ hi)
  have hcut := cutOf hw hamt
  let test : (Fin n → Word) → Word := fun S => ((w S).take ((w S).length-amount S))
  have hlast : BoolPoly (fun S => (test S).getLast?.getD false) := by
    apply (cases hcut (const [false]) (const [false]) (const [true])).congr
    intro S
    simp only [unary, List.length_replicate]
    cases (test S).getLast? with
    | none => rfl
    | some b => cases b <;> rfl
  have h := branches (NatPoly.lt hi (NatPoly.length hw)) hlast (const [false])
  apply h.congr
  intro S
  by_cases hlt : i S < (w S).length
  · simp only [decide_eq_true hlt, ite_true]
    have hn : (w S).length-amount S = i S+1 := by dsimp [amount]; omega
    dsimp only [test]
    rw [hn, List.getLast?_take]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [List.getElem?_eq_getElem hlt]
    rfl
  · simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte]
    rw [List.getElem?_eq_none (by omega)]
    rfl

/-- Polynomially bounded tabulation is implemented by captured-count iteration;
there is no list-construction oracle in the underlying Machine. -/
theorem tabulate {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    Poly (fun S => (List.range (c S)).map (fun i => p (Fin.snoc S (unary i)))) := by
  let step : (Fin (n+2) → Word) → Word := fun T => T (accum n) ++ [p (T ∘ Fin.castSucc)]
  have hstep : Poly step := by
    apply (branches (BoolPoly.rename hp Fin.castSucc) (snoc (var (accum n)) true)
      (snoc (var (accum n)) false)).congr
    intro T; dsimp [step]; cases p (T ∘ Fin.castSucc) <;> rfl
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages step S [] k =
      (List.range k).map (fun i => p (Fin.snoc S (unary i))) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Expr.stages, step, extend_accum, ih, List.range_succ, List.map_append,
        List.map_singleton]
      congr 3
      funext j
      simp
  obtain ⟨ce,C,hC,hce,hcb⟩ := hc
  have hlen (S : Fin n → Word) (N : ℕ) (hS : ∀ i, (S i).length ≤ N) : c S ≤ C N := by
    have := ce.length_le _ _ (hcb S N hS)
    simpa only [hce, unary, List.length_replicate] using this
  have h := loop ⟨ce,C,hC,hce,hcb⟩ nil hstep C hC (by
    intro S N hS k hk
    rw [hs]
    simp only [List.length_map, List.length_range]
    exact (by simpa only [unary, List.length_replicate] using hk : k ≤ c S).trans (hlen S N hS))
  apply h.congr
  intro S
  simpa only [unary, List.length_replicate] using hs S (c S)

end Poly
end WordExpressions

namespace WordExpressions
namespace Poly
variable {n : ℕ}

theorem length_bound {f : (Fin n → Word) → Word} (hf : Poly f) :
    ∃ B : ℕ → ℕ, ComputationBounds.Polynomial B ∧
      ∀ S N, (∀ i, (S i).length ≤ N) → (f S).length ≤ B N := by
  obtain ⟨e,B,hB,he,hbound⟩ := hf
  exact ⟨B,hB,fun S N hS => by rw [← he]; exact e.length_le _ _ (hbound _ _ hS)⟩

end Poly
namespace NatPoly
variable {n : ℕ}

theorem bound {f : (Fin n → Word) → ℕ} (hf : NatPoly f) :
    ∃ B : ℕ → ℕ, ComputationBounds.Polynomial B ∧
      ∀ S N, (∀ i, (S i).length ≤ N) → f S ≤ B N := by
  simpa only [unary, List.length_replicate] using Poly.length_bound hf

/-- Natural-valued iteration, represented by literal unary words. -/
def stages (f : (Fin (n+2) → Word) → ℕ) (S : Fin n → Word) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k+1 => f (Fin.snoc (Fin.snoc S (unary k)) (unary (stages f S a k)))

theorem stages_word (f : (Fin (n+2) → Word) → ℕ) (S : Fin n → Word) (a k : ℕ) :
    Expr.stages (fun T => unary (f T)) S (unary a) k = unary (stages f S a k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Expr.stages, ih, stages]

theorem loop {c a : (Fin n → Word) → ℕ} {f : (Fin (n+2) → Word) → ℕ}
    (hc : NatPoly c) (ha : NatPoly a) (hf : NatPoly f)
    (H : ℕ → ℕ) (hH : ComputationBounds.Polynomial H)
    (hstage : ∀ S N, (∀ j, (S j).length ≤ N) → ∀ i ≤ c S, stages f S (a S) i ≤ H N) :
    NatPoly (fun S => stages f S (a S) (c S)) := by
  have h := Poly.loop hc ha hf H hH (by
    intro S N hS i hi
    simpa only [stages_word, unary, List.length_replicate] using
      hstage S N hS i (by simpa only [unary, List.length_replicate] using hi))
  exact h.congr (fun S => by simpa only [unary, List.length_replicate] using stages_word f S (a S) (c S))

end NatPoly
namespace BoolPoly
variable {n : ℕ}

theorem boundedAll {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    BoolPoly (fun S => (List.range (c S)).all (fun i => p (Fin.snoc S (unary i)))) := by
  let f : (Fin (n+2) → Word) → Word := fun T =>
    boolWord (((T (accum n)).getLast?.getD false) && p (T ∘ Fin.castSucc))
  have hb : BoolPoly (fun T : Fin (n+2) → Word => (T (accum n)).getLast?.getD false) := by
    apply (Poly.cases (Poly.var _) (Poly.const [false]) (Poly.const [false]) (Poly.const [true])).congr
    intro T; dsimp only; cases (T (accum n)).getLast? with
    | none => rfl
    | some b => cases b <;> rfl
  have hf : Poly f := and hb (rename hp Fin.castSucc)
  have hs (S : Fin n → Word) (k : ℕ) : Expr.stages f S [true] k =
      boolWord ((List.range k).all (fun i => p (Fin.snoc S (unary i)))) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp [Expr.stages, f, ih, List.range_succ]
  have h := Poly.loop hc (Poly.const [true]) hf (fun _ => 1) (ComputationBounds.constant 1) (by
    intro S N hS k hk
    rw [hs]; rfl)
  exact h.congr (fun S => by simpa only [unary, List.length_replicate] using hs S (c S))

theorem boundedAny {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    BoolPoly (fun S => (List.range (c S)).any (fun i => p (Fin.snoc S (unary i)))) := by
  apply (not (boundedAll hc (not hp))).congr
  intro S
  simp [List.any_eq_not_all_not]

end BoolPoly
end WordExpressions

namespace WordExpressions
namespace Poly
variable {n m : ℕ}

theorem applyWord {f : (Fin (n+1) → Word) → Word} {g : (Fin m → Word) → Word}
    (hf : Poly f) (r : Fin n → Fin m) (hg : Poly g) :
    Poly (fun S => f (Fin.snoc (S ∘ r) (g S))) := by
  apply hf.subst
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hg
  · simpa only [Fin.snoc_castSucc, Function.comp_apply] using var (r j)

end Poly
namespace NatPoly
variable {n : ℕ}

theorem findGreatest {c : (Fin n → Word) → ℕ} {p : (Fin (n+1) → Word) → Bool}
    (hc : NatPoly c) (hp : BoolPoly p) :
    NatPoly (fun S => Nat.findGreatest (fun i => p (Fin.snoc S (unary i)) = true) (c S)) := by
  let step : (Fin (n+2) → Word) → ℕ := fun T =>
    if p (Fin.snoc (T ∘ old) (unary ((T (index n)).length+1))) then
      (T (index n)).length+1 else (T (accum n)).length
  have hp' : BoolPoly (fun T : Fin (n+2) → Word =>
      p (Fin.snoc (T ∘ old) (unary ((T (index n)).length+1)))) :=
    Poly.applyWord hp old (succ (var (index n)))
  have hstep : NatPoly step := ite hp' (succ (var (index n))) (var (accum n))
  have hs (S : Fin n → Word) (k : ℕ) : stages step S 0 k =
      Nat.findGreatest (fun i => p (Fin.snoc S (unary i)) = true) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp [stages, step, ih, Nat.findGreatest_succ]
  obtain ⟨C,hC,hcb⟩ := bound hc
  have h := loop hc (const 0) hstep C hC (by
    intro S N hS k hk
    rw [hs]
    exact (Nat.findGreatest_le k).trans (hk.trans (hcb S N hS)))
  apply h.congr
  intro S
  dsimp only
  rw [hs]

theorem div {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => f S / g S) := by
  have hp : BoolPoly (fun T : Fin (n+1) → Word =>
      decide ((T (Fin.last n)).length*g (T ∘ Fin.castSucc) ≤ f (T ∘ Fin.castSucc))) :=
    le (mul (var (Fin.last n)) (rename hg Fin.castSucc)) (rename hf Fin.castSucc)
  have hq := findGreatest hf hp
  have hb : NatPoly (fun S =>
      if decide (g S = 0) then 0 else
        Nat.findGreatest (fun i => decide (i*g S ≤ f S) = true) (f S)) := by
    apply (ite (eqtest hg (const 0)) (const 0) hq).congr
    intro S
    simp only [unary, Fin.snoc_last, List.length_replicate]
    congr 3; funext i; simp
  apply hb.congr
  intro S
  by_cases hz : g S = 0
  · simp [hz, Nat.div_zero]
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨Nat.div_le_self _ _, ?_, ?_⟩
    · intro _
      simp only [decide_eq_true_eq]
      exact (Nat.le_div_iff_mul_le (by omega)).mp (le_refl _)
    · intro i hi _
      simp only [decide_eq_true_eq]
      intro hmul
      have := (Nat.le_div_iff_mul_le (by omega)).mpr hmul
      omega

theorem mod {f g : (Fin n → Word) → ℕ} (hf : NatPoly f) (hg : NatPoly g) :
    NatPoly (fun S => f S % g S) := by
  simpa only [Nat.mod_eq_sub_mul_div] using sub hf (mul hg (div hf hg))

end NatPoly
end WordExpressions

namespace WordExpressions.Poly

theorem computes {f : (Fin 1 → Word) → Word} (hf : Poly f) :
    ∃ (M : Machine) (C d : ℕ),
      ComputesWithin M (fun w => f (fun _ => w)) (fun n => C*(n+1)^d) := by
  obtain ⟨e,B,hB,he,hbound⟩ := hf
  let D := fun n => n+B n
  have hd : ∀ n, n ≤ D n := fun n => Nat.le_add_right _ _
  have hb : ∀ w, e.Bounded (fun _ => w) (D w.length) := by
    intro w
    exact e.bounded_mono (hbound _ _ (by intro i; rfl)) (Nat.le_add_left _ _)
  obtain ⟨M,hM⟩ := e.computes D hd hb
  obtain ⟨C,d,hCd⟩ := ComputationBounds.compose e.outputBound_polynomial
    (ComputationBounds.add ComputationBounds.identity hB)
  refine ⟨M,C,d,?_⟩
  intro w
  obtain ⟨t,ht,hhalt,hout⟩ := hM w
  exact ⟨t,ht.trans (hCd w.length),hhalt,by simpa only [he] using hout⟩

end WordExpressions.Poly

end WLIdentification

end OAI
