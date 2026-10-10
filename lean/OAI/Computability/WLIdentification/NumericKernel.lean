import OAI.Computability.WLIdentification.ExponentialComputation

namespace OAI

namespace WLIdentification

namespace NumericKernel

def lookup (R : Word) (a b : ℕ) : Bool := R[Nat.pair a b]?.getD false

def digit (base v i : ℕ) : ℕ := v / base^i % base

def vectorMatch (N width : ℕ) (trans R : Word) (a z v : ℕ) : Bool :=
  (List.range width).all (fun i => (List.range N).any (fun y =>
    trans[Nat.pair a (Nat.pair z (Nat.pair i y))]?.getD false &&
      lookup R y (digit N v i)))

def countMatch (N width branch : ℕ) (active trans R : Word) (a v : ℕ) : ℕ :=
  ((List.range branch).map (fun z =>
    if lookup active a z && vectorMatch N width trans R a z v then 1 else 0)).sum

def entry (N width branch cap : ℕ) (active trans R : Word) (a b : ℕ) : Bool :=
  lookup R a b && (List.range (min (N^width) cap)).all (fun v =>
    decide (countMatch N width branch active trans R a v =
      countMatch N width branch active trans R b v))

def step (N width branch cap : ℕ) (active trans R : Word) : Word :=
  (List.range (Nat.pair N N+1)).map (fun j =>
    entry N width branch cap active trans R (Nat.unpair j).1 (Nat.unpair j).2)

def table (N width branch cap : ℕ) (active trans initial : Word) (rounds : ℕ) : Word :=
  (step N width branch cap active trans)^[rounds] initial

end NumericKernel
namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem digit {b v i : (Fin n → Word) → ℕ}
    (hb : NatPoly b) (hv : NatPoly v) (hi : NatPoly i) :
    NatPoly (fun S => NumericKernel.digit (b S) (v S) (i S)) := by
  apply (mod (div hv (cappedPow hb hi (succ hv))) hb).congr
  intro S
  simp only [div_cap, NumericKernel.digit]

end WordExpressions.NatPoly
namespace NumericKernel
open WordExpressions

/-- All loops below range over explicit unary word lengths. -/
theorem vectorMatch_poly : BoolPoly (fun S : Fin 7 → Word =>
    vectorMatch (S 0).length (S 1).length (S 2) (S 3) (S 4).length (S 5).length (S 6).length) := by
  unfold vectorMatch lookup
  apply BoolPoly.allRange (NatPoly.var 1)
  apply BoolPoly.anyRange (NatPoly.var 0)
  apply BoolPoly.and
  · word_poly
  · apply Poly.nth (Poly.var 3)
    apply NatPoly.pair (NatPoly.var (Fin.last 8))
    apply NatPoly.digit <;> word_poly

end NumericKernel
namespace NumericKernel
open WordExpressions

theorem vectorMatch_poly_of {n} {N w a z v : (Fin n → Word) → ℕ}
    {tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w)
    (ht : Poly tr) (hR : Poly R) (ha : NatPoly a) (hz : NatPoly z) (hv : NatPoly v) :
    BoolPoly (fun S => vectorMatch (N S) (w S) (tr S) (R S) (a S) (z S) (v S)) := by
  have h := vectorMatch_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),tr,R,
    fun S => unary (a S),fun S => unary (z S),fun S => unary (v S)])
    (by intro i; fin_cases i; exacts [hN,hw,ht,hR,ha,hz,hv])
  simpa [unary] using h

theorem countMatch_poly : NatPoly (fun S : Fin 8 → Word =>
    countMatch (S 0).length (S 1).length (S 2).length (S 3) (S 4) (S 5)
      (S 6).length (S 7).length) := by
  unfold countMatch
  apply NatPoly.sumRange (NatPoly.var 2)
  apply NatPoly.ite
  · apply BoolPoly.and
    · unfold lookup; word_poly
    · apply vectorMatch_poly_of <;> word_poly
  · exact NatPoly.const 1
  · exact NatPoly.const 0

theorem countMatch_poly_of {n} {N w b a v : (Fin n → Word) → ℕ}
    {ac tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w) (hb : NatPoly b)
    (hac : Poly ac) (ht : Poly tr) (hR : Poly R) (ha : NatPoly a) (hv : NatPoly v) :
    NatPoly (fun S => countMatch (N S) (w S) (b S) (ac S) (tr S) (R S) (a S) (v S)) := by
  have h := countMatch_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),
    fun S => unary (b S),ac,tr,R,fun S => unary (a S),fun S => unary (v S)])
    (by intro i; fin_cases i; exacts [hN,hw,hb,hac,ht,hR,ha,hv])
  simpa [unary] using h

theorem entry_poly : BoolPoly (fun S : Fin 9 → Word =>
    entry (S 0).length (S 1).length (S 2).length (S 3).length (S 4) (S 5) (S 6)
      (S 7).length (S 8).length) := by
  unfold entry
  apply BoolPoly.and
  · unfold lookup; word_poly
  · apply BoolPoly.allRange
    · word_poly
    · apply NatPoly.eqtest <;> apply countMatch_poly_of <;> word_poly

theorem entry_poly_of {n} {N w br c a b : (Fin n → Word) → ℕ}
    {ac tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w)
    (hbr : NatPoly br) (hc : NatPoly c) (hac : Poly ac) (ht : Poly tr) (hR : Poly R)
    (ha : NatPoly a) (hb : NatPoly b) :
    BoolPoly (fun S => entry (N S) (w S) (br S) (c S) (ac S) (tr S) (R S) (a S) (b S)) := by
  have h := entry_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),
    fun S => unary (br S),fun S => unary (c S),ac,tr,R,fun S => unary (a S),fun S => unary (b S)])
    (by intro i; fin_cases i; exacts [hN,hw,hbr,hc,hac,ht,hR,ha,hb])
  simpa [unary] using h

theorem step_poly : Poly (fun S : Fin 7 → Word =>
    step (S 0).length (S 1).length (S 2).length (S 3).length (S 4) (S 5) (S 6)) := by
  unfold step
  apply Poly.tabulateRange
  · word_poly
  · apply entry_poly_of <;> word_poly

theorem step_poly_of {n} {N w br c : (Fin n → Word) → ℕ}
    {ac tr R : (Fin n → Word) → Word} (hN : NatPoly N) (hw : NatPoly w)
    (hbr : NatPoly br) (hc : NatPoly c) (hac : Poly ac) (ht : Poly tr) (hR : Poly R) :
    Poly (fun S => step (N S) (w S) (br S) (c S) (ac S) (tr S) (R S)) := by
  have h := step_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),
    fun S => unary (br S),fun S => unary (c S),ac,tr,R])
    (by intro i; fin_cases i; exacts [hN,hw,hbr,hc,hac,ht,hR])
  simpa [unary] using h

end NumericKernel
namespace WordExpressions.Poly
variable {n : ℕ}

/-- Iteration with a proved output-length invariant.  Its loop count is a
physical unary word, not an unbounded recursion primitive. -/
theorem iterate {c b : (Fin n → Word) → ℕ} {a : (Fin n → Word) → Word}
    {f : (Fin n → Word) → Word → Word} (hc : NatPoly c) (hb : NatPoly b) (ha : Poly a)
    (hf : Poly (fun T => f (T ∘ Fin.castSucc) (T (Fin.last n))))
    (hlen : ∀ S W, (f S W).length ≤ b S) :
    Poly (fun S => (f S)^[c S] (a S)) := by
  let g : (Fin (n+2) → Word) → Word := fun T =>
    f (T ∘ Fin.castSucc ∘ Fin.castSucc) (T (Fin.last (n+1)))
  have hg : Poly g := by
    apply (hf.rename (Fin.lastCases (Fin.last (n+1)) (fun i => i.castSucc.castSucc))).congr
    intro T
    simp only [Function.comp_def, Fin.lastCases_castSucc, Fin.lastCases_last, g]
  have hs (S : Fin n → Word) (i : ℕ) : Expr.stages g S (a S) i = (f S)^[i] (a S) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [Expr.stages, Function.iterate_succ_apply']
      rw [ih]
      simp only [g, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]
  obtain ⟨A,hA,hAb⟩ := ha.length_bound
  obtain ⟨B,hB,hBb⟩ := hb.bound
  have h := loop hc ha hg (fun N => A N+B N) (ComputationBounds.add hA hB) (by
    intro S N hS i _
    rw [hs]
    cases i with
    | zero => exact (hAb S N hS).trans (Nat.le_add_right _ _)
    | succ i =>
      rw [Function.iterate_succ_apply']
      exact ((hlen S _).trans (hBb S N hS)).trans (Nat.le_add_left _ _))
  apply h.congr
  intro S
  simpa only [unary, List.length_replicate] using hs S (c S)

end WordExpressions.Poly
namespace NumericKernel
open WordExpressions

theorem table_poly : Poly (fun S : Fin 8 → Word =>
    table (S 0).length (S 1).length (S 2).length (S 3).length (S 4) (S 5) (S 6) (S 7).length) := by
  apply Poly.iterate (NatPoly.var 7)
    (b := fun S => Nat.pair (S 0).length (S 0).length+1)
  · word_poly
  · exact Poly.var 6
  · apply step_poly_of <;> word_poly
  · intro S W
    simp only [step, List.length_map, List.length_range, le_refl]

end NumericKernel

namespace NumericKernel

structure Data (N width branch : ℕ) where
  active : Fin N → Fin branch → Bool
  next : Fin N → Fin branch → Fin width → Fin N

variable {N width branch : ℕ} (D : Data N width branch)

def Data.vectors (a : Fin N) : Multiset (Fin width → Fin N) :=
  ((Finset.univ : Finset (Fin branch)).filter (fun z => D.active a z = true)).val.map (D.next a)

def Encoded (active trans : Word) : Prop :=
  (∀ (a : Fin N) (z : Fin branch), lookup active a z = D.active a z) ∧
  (∀ (a : Fin N) (z : Fin branch) (i : Fin width) (y : Fin N),
    trans[Nat.pair a (Nat.pair z (Nat.pair i y))]?.getD false = decide (D.next a z i = y))

def Represents (W : Word) (R : Fin N → Fin N → Bool) : Prop :=
  ∀ a b : Fin N, lookup W a b = R a b

theorem vectorMatch_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (a : Fin N) (z : Fin branch)
    (v : Fin (N^width)) :
    vectorMatch N width trans W a z v =
      FiniteRefinement.vectorMatch R (D.next a z) (finFunctionFinEquiv.symm v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [vectorMatch, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.and_eq_true, FiniteRefinement.vectorMatch, decide_eq_true_eq]
  constructor
  · intro h i
    obtain ⟨y,hy,ht,hm⟩ := h i i.isLt
    have ht' := he.2 a z i ⟨y,hy⟩
    have hnext : D.next a z i = ⟨y,hy⟩ := by
      simpa only [ht, decide_eq_true_eq, true_iff] using ht'.symm
    rw [hnext]
    exact (hR ⟨y,hy⟩ (finFunctionFinEquiv.symm v i)).symm.trans hm
  · intro h i hi
    let ii : Fin width := ⟨i,hi⟩
    refine ⟨D.next a z ii, (D.next a z ii).isLt, ?_, ?_⟩
    · simpa using he.2 a z ii (D.next a z ii)
    · exact (hR (D.next a z ii) (finFunctionFinEquiv.symm v ii)).trans (h ii)

end NumericKernel
namespace NumericKernel

theorem sum_range_fin (b : ℕ) (f : ℕ → ℕ) :
    ((List.range b).map f).sum = ∑ i : Fin b, f i := by
  induction b with
  | zero => simp
  | succ b ih => simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem multiset_countP_sum {A : Type} (L : Multiset A) (p : A → Prop) [DecidablePred p] :
    L.countP p = (L.map (fun x => if p x then 1 else 0)).sum := by
  induction L using Multiset.induction_on with
  | empty => simp
  | @cons a L ih => simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, ih, Nat.add_comm]

variable {N width branch : ℕ} (D : Data N width branch)

theorem countMatch_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (a : Fin N) (v : Fin (N^width)) :
    countMatch N width branch active trans W a v =
      (D.vectors a).countP (fun w => FiniteRefinement.vectorMatch R w (finFunctionFinEquiv.symm v) = true) := by
  rw [countMatch, sum_range_fin]
  simp only [Data.vectors, Multiset.countP_map, Finset.filter_val, Multiset.filter_filter]
  rw [← Multiset.countP_eq_card_filter, multiset_countP_sum]
  change (∑ z : Fin branch, _) = ∑ z : Fin branch, _
  apply Finset.sum_congr rfl
  intro z _
  rw [he.1 a z, vectorMatch_correct D he hR a z v]
  simp only [Bool.and_eq_true]
  congr 1
  exact propext and_comm

theorem entry_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (cap : ℕ) (hcap : N^width ≤ cap)
    (a b : Fin N) :
    entry N width branch cap active trans W a b = FiniteRefinement.tableStep D.vectors R a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [entry, hR a b, FiniteRefinement.tableStep, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, decide_eq_true_eq, min_eq_left hcap]
  apply and_congr Iff.rfl
  constructor
  · intro h v
    have hh := h (finFunctionFinEquiv v) (finFunctionFinEquiv v).isLt
    simpa only [countMatch_correct D he hR, Equiv.symm_apply_apply] using hh
  · intro h v hv
    rw [countMatch_correct D he hR a ⟨v,hv⟩, countMatch_correct D he hR b ⟨v,hv⟩]
    exact h (finFunctionFinEquiv.symm ⟨v,hv⟩)

theorem lookup_step {active trans W : Word} (cap : ℕ) (a b : Fin N) :
    lookup (step N width branch cap active trans W) a b =
      entry N width branch cap active trans W a b := by
  have hb : Nat.pair a.val b.val < Nat.pair N N+1 := by
    have h1 := Nat.pair_lt_pair_left b.val a.isLt
    have h2 := Nat.pair_lt_pair_right N b.isLt
    omega
  simp only [lookup, step, List.getElem?_map, List.getElem?_range hb, Option.map_some,
    Option.getD_some, Nat.unpair_pair]

theorem step_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (cap : ℕ) (hcap : N^width ≤ cap) :
    Represents (step N width branch cap active trans W) (FiniteRefinement.tableStep D.vectors R) := by
  intro a b
  rw [lookup_step]
  exact entry_correct D he hR cap hcap a b

theorem table_correct {active trans W : Word} (he : Encoded D active trans)
    {R : Fin N → Fin N → Bool} (hR : Represents W R) (cap : ℕ) (hcap : N^width ≤ cap) (s : ℕ) :
    Represents (table N width branch cap active trans W s) (FiniteRefinement.table D.vectors R s) := by
  induction s with
  | zero => exact hR
  | succ s ih =>
    simp only [table, FiniteRefinement.table, Function.iterate_succ_apply'] at *
    exact step_correct D he ih cap hcap

end NumericKernel

end WLIdentification

end OAI
