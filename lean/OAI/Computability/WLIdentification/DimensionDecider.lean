import OAI.Computability.WLIdentification.RefinementCorrectness

namespace OAI

namespace WLIdentification

namespace DimensionDecider

def matrix (n : ℕ) (w : Word) : Word := (w.drop (n+1)).take (n*n)
def bits (n : ℕ) (w : Word) : Word := w.drop (n+1+n*n)
def valid (n : ℕ) (w : Word) : Bool :=
  decide (0<n) && decide (w.take (n+1) = List.replicate n true ++ [false]) &&
    decide ((matrix n w).length=n*n) && (bits n w)[0]?.getD false

def identifies (n k cap : ℕ) (W : Word) : Bool :=
  (List.range (min (2^(n*n)) cap)).all (fun x =>
    !(NumericWL.equivalent n k cap W (NumericGraph.mate n x)) ||
      NumericGraph.iso n cap W (NumericGraph.mate n x))

def atOrder (n cap : ℕ) (w : Word) : Bool :=
  valid n w && NumericGraph.simple n (matrix n w) &&
    identifies n (min (binaryValue (bits n w)) (max 2 n)) cap (matrix n w)

def decideWord (cap : ℕ) (w : Word) : Bool :=
  (List.range (w.length+1)).any (fun n => atOrder n cap w)

def budget (m : ℕ) : ℕ := 2^(64*(m+1)^6)

end DimensionDecider

namespace NumericGraph

@[simp] theorem ofWord_matrixWord (G : Graph) : ofWord G.order (matrixWord G) (simple_matrixWord G) = G := by
  apply Graph.ext (ofWord G.order (matrixWord G) (simple_matrixWord G)) G rfl
  intro i j
  exact edge_matrixWord G i j

@[simp] theorem mate_simple (n x : ℕ) : simple n (mate n x) = true := by
  apply (simple_true _ _).mpr
  constructor
  · intro i; rw [edge_mate]; exact (mateGraph n x).loopless i
  · intro i j; rw [edge_mate, edge_mate]; exact (mateGraph n x).symmetric i j

@[simp] theorem ofWord_mate (n x : ℕ) : ofWord n (mate n x) (mate_simple n x) = mateGraph n x := by
  apply Graph.ext (ofWord n (mate n x) (mate_simple n x)) (mateGraph n x) rfl
  exact edge_mate n x

@[simp] theorem matrixWord_ofWord (n : ℕ) (W : Word) (h : simple n W = true) (hl : W.length=n*n) :
    matrixWord (ofWord n W h) = W := by
  apply List.ext_getElem (by simp [hl])
  intro t ht ht'
  have hn : 0<n := by have := Nat.zero_lt_of_lt ht'; rw [hl] at this; nlinarith
  let i : Fin n := ⟨t/n, (Nat.div_lt_iff_lt_mul hn).mpr (by simpa [hl] using ht')⟩
  let j : Fin n := ⟨t%n, Nat.mod_lt _ hn⟩
  have hij : i.val*n+j.val=t := by simpa only [i, j, Nat.mul_comm] using Nat.div_add_mod t n
  have hh := edge_matrixWord (ofWord n W h) i j
  change (matrixWord (ofWord n W h))[i.val*n+j.val]?.getD false = W[i.val*n+j.val]?.getD false at hh
  rw [hij, List.getElem?_eq_getElem ht, List.getElem?_eq_getElem ht'] at hh
  exact hh

end NumericGraph

/-- Positive-dimensional equivalence always fixes the order, even for the
ordinary-neighbor dimension-one convention. -/
theorem equivalent_order {G H : Graph} {k : ℕ} (hk : 0<k) (h : Equivalent k G H) : G.order=H.order := by
  by_cases hk1 : k=1
  · subst k
    have hh := congrArg Multiset.card ((show ∀ s, neighborHistogram G s=neighborHistogram H s from h) 0)
    simpa [neighborHistogram] using hh
  · obtain ⟨e,_⟩ := equivalent_degreeBijection (by omega) h
    simpa using Fintype.card_congr e

/-- Exhaustive masks suffice for all mates because order equality is proved,
not inserted as an extra hypothesis in identification. -/
theorem identifies_iff_masks (G : Graph) (k : ℕ) (hk : 0<k) : Identifies k G ↔
    ∀ x<2^(G.order*G.order), Equivalent k G (NumericGraph.mateGraph G.order x) →
      Isomorphic G (NumericGraph.mateGraph G.order x) := by
  constructor
  · intro h x _; exact h _
  · intro h H hH
    have hn := equivalent_order hk hH
    let x := NumericGraph.number (matrixWord H)
    have hx : x<2^(G.order*G.order) := by
      simpa [x, matrixWord_length, hn] using NumericGraph.number_lt (matrixWord H)
    have he : NumericGraph.mateGraph G.order x=H := by
      cases H with
      | mk m ed hs hl =>
        dsimp only at hn
        subst m
        apply Graph.ext (NumericGraph.mateGraph G.order x) ⟨G.order,ed,hs,hl⟩ rfl
        intro i j
        exact NumericGraph.mateGraph_covers ⟨G.order,ed,hs,hl⟩ i j
    simpa only [he] using h x hx (by simpa only [he] using hH)

namespace DimensionDecider

theorem valid_iff (n : ℕ) (w : Word) : valid n w = true ↔
    0<n ∧ w.take (n+1) = List.replicate n true ++ [false] ∧
      (matrix n w).length=n*n ∧ ∃ t, bits n w = true::t := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq]
  have hb : (bits n w)[0]?.getD false = true ↔ ∃ t, bits n w=true::t := by
    cases bits n w with
    | nil => simp
    | cons b w => cases b <;> simp
  rw [hb]
  tauto

theorem binaryValue_leading_pos {w : Word} (h : ∃ t, w=true::t) : 0<binaryValue w := by
  obtain ⟨t,rfl⟩ := h
  have ha (t : Word) (c : ℕ) (hc : 0<c) : 0<t.foldl (fun z b => 2*z+if b then 1 else 0) c := by
    induction t generalizing c with
    | nil => exact hc
    | cons b t ih =>
      apply ih
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  exact ha t 1 (by decide)

theorem input_valid (G : Graph) (w : Word) (hn : 0<G.order) (hb : ∃ t, w=true::t) :
    valid G.order (inputWord G w) = true := by
  apply (valid_iff _ _).mpr
  have hdrop : (inputWord G w).drop (G.order+1)=matrixWord G++w := by
    simp [inputWord, List.drop_append, List.drop_replicate]
  refine ⟨hn, ?_, ?_, ?_⟩
  · have : G.order+1 = (List.replicate G.order true ++ [false]).length := by simp
    rw [this]
    unfold inputWord
    rw [List.append_assoc (List.replicate G.order true ++ [false])]
    exact List.take_left
  · simp [matrix, hdrop]
  · simpa only [bits, ← List.drop_drop, hdrop, ← matrixWord_length G, List.drop_left] using hb

theorem input_extract (G : Graph) (w : Word) :
    matrix G.order (inputWord G w)=matrixWord G ∧ bits G.order (inputWord G w)=w := by
  have hdrop : (inputWord G w).drop (G.order+1)=matrixWord G++w := by
    simp [inputWord, List.drop_append, List.drop_replicate]
  constructor
  · simpa only [matrix, hdrop, ← matrixWord_length G] using (List.take_left (l₁ := matrixWord G) (l₂ := w))
  · simpa only [bits, ← List.drop_drop, hdrop, ← matrixWord_length G] using (List.drop_left (l₁ := matrixWord G) (l₂ := w))

theorem reconstruct {n : ℕ} {w : Word} (hv : valid n w=true)
    (hs : NumericGraph.simple n (matrix n w)=true) :
    w=inputWord (NumericGraph.ofWord n (matrix n w) hs) (bits n w) := by
  obtain ⟨_,hh,hl,_⟩ := (valid_iff n w).mp hv
  rw [inputWord, NumericGraph.matrixWord_ofWord _ _ _ hl]
  change w = (List.replicate n true ++ [false]) ++ matrix n w ++ bits n w
  rw [← hh, List.append_assoc]
  have hd : matrix n w ++ bits n w = w.drop (n+1) := by
    simp only [matrix, bits, ← List.drop_drop]
    exact List.take_append_drop _ _
  rw [hd, List.take_append_drop]

end DimensionDecider

namespace DimensionDecider

theorem budget_bounds {n k m : ℕ} (hn : n ≤ m) (hk : k ≤ max 2 n) :
    n+n  ≤  budget m ∧ n^k  ≤  budget m ∧ (n^k+n^k)^k  ≤  budget m ∧ n^n ≤ budget m ∧ 2^(n*n) ≤ budget m := by
  let s := m+1
  change n+n ≤ 2^(64*s^6) ∧ n^k ≤ 2^(64*s^6) ∧ (n^k+n^k)^k ≤ 2^(64*s^6) ∧ n^n ≤ 2^(64*s^6) ∧ 2^(n*n) ≤ 2^(64*s^6)
  have hs : 1 ≤ s := by omega
  have ns : n ≤ s := by omega
  have ks : k ≤ 2*s := by
    have : max 2 n ≤ 2*s := max_le (by omega) (by omega)
    exact hk.trans this
  have hs2 : s ≤ s^2 := Nat.le_pow (by decide)
  have hs6 : s^2 ≤ s^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs3 : s^3 ≤ s^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have base : n ≤ 2^s := ns.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have expbound : 2*s^2 ≤ 64*s^6 := by omega
  have nnpow : n^n ≤ 2^(s^2) := by
    calc n^n  ≤  (2^s)^n := Nat.pow_le_pow_left base _
      _ = 2^(s*n) := (pow_mul _ _ _).symm
      _  ≤  2^(s^2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have nkt : n^k ≤ 2^(2*s^2) := by
    calc n^k  ≤  (2^s)^k := Nat.pow_le_pow_left base _
      _ = 2^(s*k) := (pow_mul _ _ _).symm
      _  ≤  2^(2*s^2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have nt : n^k+n^k ≤ 2^(1+2*s^2) := by
    rw [pow_add, pow_one]
    omega
  have main : (n^k+n^k)^k ≤ 2^(64*s^6) := by
    calc (n^k+n^k)^k  ≤  (2^(1+2*s^2))^k := Nat.pow_le_pow_left nt _
      _ = 2^((1+2*s^2)*k) := (pow_mul _ _ _).symm
      _  ≤  2^(64*s^6) := Nat.pow_le_pow_right (by decide) (by
        have ht := Nat.mul_le_mul_left (1+2*s^2) ks
        have h3 : (1+2*s^2)*(2*s)=2*s+4*s^3 := by ring
        rw [h3] at ht
        omega)
  have nm : n*n ≤ 64*s^6 := by nlinarith
  refine ⟨?_, nkt.trans (Nat.pow_le_pow_right (by decide) expbound), main,
    nnpow.trans (Nat.pow_le_pow_right (by decide) (by omega)), Nat.pow_le_pow_right (by decide) nm⟩
  calc n+n  ≤  2*2^s := by omega
    _ = 2^(s+1) := (Nat.mul_comm 2 (2^s)).trans (pow_succ 2 s).symm
    _  ≤  2^(64*s^6) := Nat.pow_le_pow_right (by decide) (by omega)

end DimensionDecider

namespace NumericWL

theorem equivalent_correct (n k cap : ℕ) (W V : Word)
    (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (hk : 0 < k) (hn : n+n ≤ cap) (ht : n^k ≤ cap) (hp : (n^k+n^k)^k ≤ cap) :
    equivalent n k cap W V=true ↔ Equivalent k (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) := by
  by_cases h : k=1
  · subst k; rw [equivalent, ite_eq_left rfl]; exact neighbor_correct n cap W V hW hV hn
  · rw [equivalent, ite_eq_right h]; exact tuple_correct n k cap W V hW hV hk h ht hp

end NumericWL
namespace DimensionDecider

theorem identifies_correct (n k cap : ℕ) (W : Word) (hW : NumericGraph.simple n W=true)
    (hk : 0 < k) (hn : n+n ≤ cap) (ht : n^k ≤ cap) (hp : (n^k+n^k)^k ≤ cap)
    (he : n^n ≤ cap) (hm : 2^(n*n) ≤ cap) :
    identifies n k cap W=true ↔ Identifies k (NumericGraph.ofWord n W hW) := by
  rw [identifies_iff_masks _ _ hk]
  simp only [identifies, min_eq_left hm, List.all_eq_true, List.mem_range]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro _
  have hbool (a b : Bool) : (!a || b)=true ↔ (a=true → b=true) := by cases a <;> cases b <;> decide
  rw [hbool, NumericWL.equivalent_correct n k cap W (NumericGraph.mate n x) hW (NumericGraph.mate_simple n x)
    hk hn ht hp, NumericGraph.iso_correct n cap W (NumericGraph.mate n x) hW (NumericGraph.mate_simple n x) he,
    NumericGraph.ofWord_mate]

theorem capped_identifies (G : Graph) (k : ℕ) (hk : 0 < k) :
    Identifies (min k (max 2 G.order)) G ↔ WLdim G ≤ k := by
  have hm : 0 < max 2 G.order := by have := le_max_left 2 G.order; omega
  have hd : WLdim G ≤ max 2 G.order := (WLdim_le_iff hm).mpr (identifies_order G)
  rw [← WLdim_le_iff (lt_min hk hm)]
  omega

theorem decideWord_correct (w : Word) : decideWord (budget w.length) w=true ↔ w∈dimensionLanguage := by
  simp only [decideWord, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨n,hn,ha⟩
    have hn' : n ≤ w.length := by omega
    simp only [atOrder, Bool.and_eq_true] at ha
    obtain ⟨⟨hv,hs⟩,hi⟩ := ha
    obtain ⟨hpos,_,_,hb⟩ := (valid_iff n w).mp hv
    have hk := binaryValue_leading_pos hb
    have hc : 0 < min (binaryValue (bits n w)) (max 2 n) := lt_min hk (by have := le_max_left 2 n; omega)
    obtain ⟨b1,b2,b3,b4,b5⟩ := budget_bounds hn' (min_le_right (binaryValue (bits n w)) (max 2 n))
    have hI := (identifies_correct _ _ _ _ hs hc b1 b2 b3 b4 b5).mp hi
    have hd := (capped_identifies (NumericGraph.ofWord n (matrix n w) hs) _ hk).mp hI
    exact ⟨NumericGraph.ofWord n (matrix n w) hs, bits n w, hpos, hb, hk, reconstruct hv hs, hd⟩
  · rintro ⟨G,B,hG,hB,hk,rfl,hd⟩
    let w := inputWord G B
    have hn : G.order ≤ w.length := by simp [w, inputWord]
    refine ⟨G.order, by dsimp only [w] at hn; omega, ?_⟩
    have hv := input_valid G B hG hB
    obtain ⟨hmat,hbits⟩ := input_extract G B
    change atOrder G.order (budget w.length) w=true
    simp only [atOrder, w, hmat, hbits, hv, NumericGraph.simple_matrixWord, Bool.true_and]
    have hc : 0 < min (binaryValue B) (max 2 G.order) := lt_min hk (by have := le_max_left 2 G.order; omega)
    obtain ⟨b1,b2,b3,b4,b5⟩ := budget_bounds hn (min_le_right (binaryValue B) (max 2 G.order))
    rw [identifies_correct _ _ _ _ (NumericGraph.simple_matrixWord G) hc b1 b2 b3 b4 b5,
      NumericGraph.ofWord_matrixWord, capped_identifies G _ hk]
    exact hd

end DimensionDecider

namespace DimensionDecider
open WordExpressions

theorem matrix_poly {m} {n : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hw : Poly w) : Poly (fun S => matrix (n S) (w S)) :=
  Poly.take (Poly.dropPrefix hw (NatPoly.succ hn)) (hn.mul hn)

theorem bits_poly {m} {n : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hw : Poly w) : Poly (fun S => bits (n S) (w S)) :=
  Poly.dropPrefix hw ((NatPoly.succ hn).add (hn.mul hn))

theorem valid_poly {m} {n : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hw : Poly w) : BoolPoly (fun S => valid (n S) (w S)) :=
  BoolPoly.and (BoolPoly.and (BoolPoly.and (NatPoly.lt (NatPoly.const 0) hn)
    (Poly.eqtest (Poly.take hw (NatPoly.succ hn))
      (Poly.append (Poly.replicate hn true) (WordExpressions.Poly.const [false]))))
    (NatPoly.eqtest (NatPoly.length (matrix_poly hn hw)) (hn.mul hn)))
    (Poly.nth (bits_poly hn hw) (NatPoly.const 0))

theorem identifies_poly : BoolPoly (fun S : Fin 4 → Word =>
    identifies (S 0).length (S 1).length (S 2).length (S 3)) := by
  unfold identifies
  apply BoolPoly.allRange
  · word_poly
  · apply BoolPoly.or
    · apply BoolPoly.not
      apply NumericWL.equivalent_poly_of
      · word_poly
      · word_poly
      · word_poly
      · word_poly
      · apply NumericGraph.mate_poly_of <;> word_poly
    · apply NumericGraph.iso_poly_of
      · word_poly
      · word_poly
      · word_poly
      · apply NumericGraph.mate_poly_of <;> word_poly

theorem identifies_poly_of {m} {n k c : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (hc : NatPoly c) (hW : Poly W) :
    BoolPoly (fun S => identifies (n S) (k S) (c S) (W S)) := by
  have h := identifies_poly.subst (g := ![fun S => unary (n S), fun S => unary (k S),
    fun S => unary (c S), W]) (by intro i; fin_cases i; exacts [hn,hk,hc,hW])
  simpa [unary] using h

theorem atOrder_poly {m} {n c : (Fin m → Word) → ℕ} {w : (Fin m → Word) → Word}
    (hn : NatPoly n) (hc : NatPoly c) (hw : Poly w) : BoolPoly (fun S => atOrder (n S) (c S) (w S)) :=
  BoolPoly.and (BoolPoly.and (valid_poly hn hw) (NumericGraph.simple_poly_of hn (matrix_poly hn hw)))
    (identifies_poly_of hn (NatPoly.decode (bits_poly hn hw) (NatPoly.max (NatPoly.const 2) hn))
      hc (matrix_poly hn hw))

theorem decideWord_poly : BoolPoly (fun S : Fin 2 → Word => decideWord (S 1).length (S 0)) := by
  unfold decideWord
  apply BoolPoly.anyRange (NatPoly.succ (NatPoly.var 0))
  apply atOrder_poly <;> word_poly

end DimensionDecider

/-- Membership for the literal parser, all-mates identification, and finite-alphabet tape model. -/
theorem dimensionLanguage_inEXPTIME : InEXPTIME dimensionLanguage := by
  apply WordExpressions.inEXPTIME_of_budget 64 6 DimensionDecider.decideWord_poly
  intro w
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, WordExpressions.unary, List.length_replicate]
  exact DimensionDecider.decideWord_correct w

end WLIdentification

end OAI
