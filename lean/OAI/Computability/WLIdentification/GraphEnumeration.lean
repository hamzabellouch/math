import OAI.Computability.WLIdentification.NumericKernel

namespace OAI

namespace WLIdentification

namespace NumericGraph

/-- Row-major access, with a total default outside the matrix. -/
def edge (n : ℕ) (W : Word) (i j : ℕ) : Bool := W[i*n+j]?.getD false

def simple (n : ℕ) (W : Word) : Bool :=
  (List.range n).all (fun i => !edge n W i i &&
    (List.range n).all (fun j => decide (edge n W i j = edge n W j i)))

def iso (n cap : ℕ) (W V : Word) : Bool :=
  (List.range (min (n^n) cap)).any (fun f => (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      decide ((NumericKernel.digit n f i = NumericKernel.digit n f j) = (i=j)) &&
      decide (edge n W i j = edge n V (NumericKernel.digit n f i) (NumericKernel.digit n f j)))))

/-- A canonically normalized mate: every simple graph occurs among these
masks, while diagonal/asymmetric mask bits do not admit malformed graphs. -/
def mateEdge (n mask i j : ℕ) : Bool :=
  decide (i ≠ j) && mask.testBit (min i j*n+max i j)

def mate (n mask : ℕ) : Word :=
  (List.range (n*n)).map (fun t => mateEdge n mask (t/n) (t%n))

end NumericGraph
namespace WordExpressions.BoolPoly
variable {n : ℕ}

theorem eqtest {p q : (Fin n → Word) → Bool} (hp : BoolPoly p) (hq : BoolPoly q) :
    BoolPoly (fun S => decide (p S=q S)) := by
  apply (or (and hp hq) (and (not hp) (not hq))).congr
  intro S
  dsimp only
  cases p S <;> cases q S <;> rfl

theorem propEq {p q : (Fin n → Word) → Prop} [∀ S, Decidable (p S)] [∀ S, Decidable (q S)]
    (hp : BoolPoly (fun S => decide (p S))) (hq : BoolPoly (fun S => decide (q S))) :
    BoolPoly (fun S => decide (p S = q S)) := by
  apply (eqtest hp hq).congr
  intro S
  by_cases h : p S <;> by_cases h' : q S <;> simp [h,h']

end WordExpressions.BoolPoly
namespace NumericGraph
open WordExpressions

theorem edge_poly {m} {n i j : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (hn : NatPoly n) (hW : Poly W) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => edge (n S) (W S) (i S) (j S)) :=
  Poly.nth hW (NatPoly.add (NatPoly.mul hi hn) hj)

theorem simple_poly : BoolPoly (fun S : Fin 2 → Word => simple (S 0).length (S 1)) := by
  unfold simple
  apply BoolPoly.allRange (NatPoly.var 0)
  apply BoolPoly.and
  · apply BoolPoly.not
    apply edge_poly <;> word_poly
  · apply BoolPoly.allRange (NatPoly.var 0)
    apply BoolPoly.eqtest <;> apply edge_poly <;> word_poly

theorem iso_poly : BoolPoly (fun S : Fin 4 → Word => iso (S 0).length (S 1).length (S 2) (S 3)) := by
  unfold iso
  apply BoolPoly.anyRange
  · word_poly
  · apply BoolPoly.allRange (NatPoly.var 0)
    apply BoolPoly.allRange (NatPoly.var 0)
    apply BoolPoly.and
    · apply BoolPoly.propEq
      · apply NatPoly.eqtest <;> apply NatPoly.digit <;> word_poly
      · word_poly
    · apply BoolPoly.eqtest
      · apply edge_poly <;> word_poly
      · apply edge_poly
        · word_poly
        · word_poly
        · apply NatPoly.digit <;> word_poly
        · apply NatPoly.digit <;> word_poly

theorem mateEdge_poly {m} {n x i j : (Fin m → Word) → ℕ}
    (hn : NatPoly n) (hx : NatPoly x) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => mateEdge (n S) (x S) (i S) (j S)) := by
  apply (BoolPoly.and (BoolPoly.not (NatPoly.eqtest hi hj))
    (NatPoly.testBit hx (NatPoly.add (NatPoly.mul (NatPoly.min hi hj) hn) (NatPoly.max hi hj)))).congr
  intro S
  simp only [mateEdge, decide_not]

theorem mate_poly : Poly (fun S : Fin 2 → Word => mate (S 0).length (S 1).length) := by
  unfold mate
  apply Poly.tabulateRange
  · word_poly
  · apply mateEdge_poly <;> word_poly

end NumericGraph

namespace NumericGraph

/-- Entries of a rectangular row-major serialization. -/
theorem rows_entry (n m : ℕ) (f : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    (((List.ofFn fun a => List.ofFn (f a)).flatten)[i.val*m+j.val]?).getD false = f i j := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun a => ?_) i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getElem?_append_left (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp only [List.length_ofFn, Fin.val_succ]; nlinarith)]
      simp only [List.length_ofFn, Fin.val_succ]
      rw [show (a.val+1)*m+j.val-m = a.val*m+j.val by simp only [Nat.add_mul, one_mul]; omega]
      exact ih (fun x => f x.succ) a

@[simp] theorem edge_matrixWord (G : Graph) (i j : Fin G.order) :
    edge G.order (matrixWord G) i j = G.edge i j := rows_entry _ _ _ i j

theorem simple_true (n : ℕ) (W : Word) : simple n W = true ↔
    (∀ i : Fin n, edge n W i i = false) ∧
    (∀ i j : Fin n, edge n W i j = edge n W j i) := by
  simp only [simple, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun i => by simpa using (h i i.isLt).1, fun i j => (h i i.isLt).2 j j.isLt⟩
  · rintro ⟨hl,hs⟩ i hi
    exact ⟨by simpa using hl ⟨i,hi⟩, fun j hj => hs ⟨i,hi⟩ ⟨j,hj⟩⟩

abbrev ofWord (n : ℕ) (W : Word) (h : simple n W = true) : Graph where
  order := n
  edge i j := edge n W i j
  symmetric := (simple_true n W).mp h |>.2
  loopless := (simple_true n W).mp h |>.1

@[simp] theorem simple_matrixWord (G : Graph) : simple G.order (matrixWord G) = true :=
  (simple_true _ _).mpr ⟨fun i => by simpa using G.loopless i,
    fun i j => by simpa using G.symmetric i j⟩

def mateGraph (n mask : ℕ) : Graph where
  order := n
  edge i j := mateEdge n mask i j
  symmetric i j := by simp only [mateEdge, ne_comm, min_comm, max_comm]
  loopless i := by simp [mateEdge]

@[simp] theorem edge_mate (n mask : ℕ) (i j : Fin n) :
    edge n (mate n mask) i j = mateEdge n mask i j := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hij : i.val*n+j.val < n*n := by nlinarith [i.isLt,j.isLt]
  simp only [edge, mate, List.getElem?_map, List.getElem?_range hij, Option.map_some, Option.getD_some]
  rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt j.isLt]

/-- Little-endian packing, used solely for proving exhaustive mask coverage. -/
def number : Word → ℕ
  | [] => 0
  | b::w => Nat.bit b (number w)

theorem number_lt (W : Word) : number W < 2^W.length := by
  induction W with
  | nil => decide
  | cons b W ih =>
    simp only [number, List.length_cons, pow_succ, Nat.bit_val]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

@[simp] theorem testBit_number (W : Word) (i : ℕ) :
    (number W).testBit i = W[i]?.getD false := by
  induction W generalizing i with
  | nil => simp [number]
  | cons b W ih =>
    cases i with
    | zero => simp [number]
    | succ i => simpa only [number, Nat.testBit_bit_succ, List.getElem?_cons_succ] using ih i

theorem mateGraph_covers (G : Graph) :
    ∀ i j : Fin G.order, (mateGraph G.order (number (matrixWord G))).edge i j = G.edge i j := by
  intro i j
  change mateEdge G.order (number (matrixWord G)) i j = _
  by_cases he : i=j
  · subst j
    simpa [mateEdge] using (G.loopless i).symm
  · have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
    simp only [mateEdge, hv, ne_eq, not_false_eq_true, decide_true, Bool.true_and, testBit_number]
    by_cases h : i.val ≤ j.val
    · rw [min_eq_left h, max_eq_right h]
      exact edge_matrixWord G i j
    · rw [min_eq_right (by omega), max_eq_left (by omega)]
      exact (edge_matrixWord G j i).trans (G.symmetric j i)

theorem iso_correct (n cap : ℕ) (W V : Word) (hsW : simple n W = true) (hsV : simple n V = true)
    (hcap : n^n ≤ cap) :
    iso n cap W V = true ↔ Isomorphic (ofWord n W hsW) (ofWord n V hsV) := by
  simp only [iso, min_eq_left hcap, List.any_eq_true, List.mem_range, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨f,hf,h⟩
    let d : Fin n → Fin n := finFunctionFinEquiv.symm ⟨f,hf⟩
    have hd : Function.Injective d := by
      intro i j hij
      have hh := (h i i.isLt j j.isLt).1
      have he : NumericKernel.digit n f i = NumericKernel.digit n f j := congrArg Fin.val hij
      exact Fin.ext (Eq.mp hh he)
    have hb : Function.Bijective d := (Finite.injective_iff_bijective).mp hd
    refine ⟨Equiv.ofBijective d hb, ?_⟩
    intro i j
    exact (h i i.isLt j j.isLt).2
  · rintro ⟨e,he⟩
    let c := finFunctionFinEquiv e
    refine ⟨c,c.isLt,?_⟩
    intro i hi j hj
    have hd (a : Fin n) : NumericKernel.digit n c a = (e a).val :=
      congrArg (fun f => (f a).val) (finFunctionFinEquiv.symm_apply_apply e)
    rw [hd ⟨i,hi⟩, hd ⟨j,hj⟩]
    refine ⟨propext ?_, ?_⟩
    · exact ⟨fun h => congrArg Fin.val (e.injective (Fin.ext h)),
        fun h => congrArg (fun x : Fin n => (e x).val) (Fin.ext h)⟩
    · exact he ⟨i,hi⟩ ⟨j,hj⟩

end NumericGraph

end WLIdentification

end OAI
