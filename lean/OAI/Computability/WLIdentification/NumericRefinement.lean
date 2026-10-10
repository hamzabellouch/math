import OAI.Computability.WLIdentification.GraphEnumeration

namespace OAI

namespace WLIdentification

namespace NumericWL
open NumericKernel

def left (t a : ℕ) : Bool := decide (a<t)
def code (t a : ℕ) : ℕ := if a<t then a else a-t

def pairTable (N : ℕ) (p : ℕ → ℕ → Bool) : Word :=
  (List.range (Nat.pair N N+1)).map (fun x => p x.unpair.1 x.unpair.2)

def transTable (N width branch : ℕ) (p : ℕ → ℕ → ℕ → ℕ → Bool) : Word :=
  (List.range (Nat.pair N (Nat.pair branch (Nat.pair width N))+1)).map (fun x =>
    p x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2.unpair.1 x.unpair.2.unpair.2.unpair.2)

def equalCounts (t : ℕ) (W : Word) : Bool :=
  (List.range (t+t)).all (fun a => decide (
    ((List.range t).map (fun b => if lookup W b a then 1 else 0)).sum =
    ((List.range t).map (fun b => if lookup W (t+b) a then 1 else 0)).sum))

def selectedEdge (n t : ℕ) (W V : Word) (a i j : ℕ) : Bool :=
  if left t a then NumericGraph.edge n W i j else NumericGraph.edge n V i j

def neighborActive (n : ℕ) (W V : Word) (a z : ℕ) : Bool :=
  selectedEdge n n W V a (code n a) z

def neighborTrans (n a z _i y : ℕ) : Bool :=
  decide (left n a = left n y) && decide (code n y = z)

def neighbor (n cap : ℕ) (W V : Word) : Bool :=
  let N := n+n
  equalCounts n (table N 1 n cap (pairTable N (neighborActive n W V))
    (transTable N 1 n (neighborTrans n)) (pairTable N (fun _ _ => true)) (N*N))

def tupleInitial (n k t : ℕ) (W V : Word) (a b : ℕ) : Bool :=
  (List.range k).all (fun i => (List.range k).all (fun j =>
    decide ((digit n (code t a) i = digit n (code t a) j) =
      (digit n (code t b) i = digit n (code t b) j)) &&
    decide (selectedEdge n t W V a (digit n (code t a) i) (digit n (code t a) j) =
      selectedEdge n t W V b (digit n (code t b) i) (digit n (code t b) j))))

def tupleTrans (n k t a z i y : ℕ) : Bool :=
  decide (left t a = left t y) && (List.range k).all (fun j =>
    decide (digit n (code t y) j = if j=i then z else digit n (code t a) j))

def tuple (n k cap : ℕ) (W V : Word) : Bool :=
  let t := min (n^k) cap
  let N := t+t
  equalCounts t (table N k n cap (pairTable N (fun _ _ => true))
    (transTable N k n (tupleTrans n k t)) (pairTable N (tupleInitial n k t W V)) (N*N))

def equivalent (n k cap : ℕ) (W V : Word) : Bool :=
  if k=1 then neighbor n cap W V else tuple n k cap W V

end NumericWL

namespace NumericWL
open WordExpressions

theorem left_poly {m} {t a : (Fin m → Word) → ℕ} (ht : NatPoly t) (ha : NatPoly a) :
    BoolPoly (fun S => left (t S) (a S)) := NatPoly.lt ha ht

theorem code_poly {m} {t a : (Fin m → Word) → ℕ} (ht : NatPoly t) (ha : NatPoly a) :
    NatPoly (fun S => code (t S) (a S)) := NatPoly.iteProp (NatPoly.lt ha ht) ha (NatPoly.sub ha ht)

theorem selectedEdge_poly {m} {n t a i j : (Fin m → Word) → ℕ}
    {W V : (Fin m → Word) → Word} (hn : NatPoly n) (ht : NatPoly t) (hW : Poly W) (hV : Poly V)
    (ha : NatPoly a) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => selectedEdge (n S) (t S) (W S) (V S) (a S) (i S) (j S)) :=
  BoolPoly.ite (left_poly ht ha) (NumericGraph.edge_poly hn hW hi hj) (NumericGraph.edge_poly hn hV hi hj)

theorem equalCounts_poly : BoolPoly (fun S : Fin 2 → Word => equalCounts (S 0).length (S 1)) := by
  unfold equalCounts
  apply BoolPoly.allRange
  · word_poly
  · apply NatPoly.eqtest <;> apply NatPoly.sumRange
    · word_poly
    · apply NatPoly.ite
      · unfold NumericKernel.lookup
        word_poly
      · word_poly
      · word_poly
    · word_poly
    · apply NatPoly.ite
      · unfold NumericKernel.lookup
        word_poly
      · word_poly
      · word_poly

theorem neighborActive_poly : BoolPoly (fun S : Fin 5 → Word =>
    neighborActive (S 0).length (S 1) (S 2) (S 3).length (S 4).length) := by
  unfold neighborActive
  apply selectedEdge_poly <;> first | apply code_poly <;> word_poly | word_poly

theorem neighborTrans_poly : BoolPoly (fun S : Fin 5 → Word =>
    neighborTrans (S 0).length (S 1).length (S 2).length (S 3).length (S 4).length) := by
  unfold neighborTrans
  apply BoolPoly.and
  · apply BoolPoly.eqtest <;> apply left_poly <;> word_poly
  · apply NatPoly.eqtest
    · apply code_poly <;> word_poly
    · word_poly

theorem tupleInitial_poly : BoolPoly (fun S : Fin 7 → Word => tupleInitial
    (S 0).length (S 1).length (S 2).length (S 3) (S 4) (S 5).length (S 6).length) := by
  unfold tupleInitial
  apply BoolPoly.allRange (NatPoly.var 1)
  apply BoolPoly.allRange (NatPoly.var 1)
  apply BoolPoly.and
  · apply BoolPoly.propEq <;> apply NatPoly.eqtest <;> apply NatPoly.digit
    all_goals first | apply code_poly <;> word_poly | word_poly
  · apply BoolPoly.eqtest <;> apply selectedEdge_poly
    all_goals repeat' first | apply NatPoly.digit | apply code_poly | solve | word_poly

theorem tupleTrans_poly : BoolPoly (fun S : Fin 7 → Word => tupleTrans
    (S 0).length (S 1).length (S 2).length (S 3).length (S 4).length (S 5).length (S 6).length) := by
  unfold tupleTrans
  apply BoolPoly.and
  · apply BoolPoly.eqtest <;> apply left_poly <;> word_poly
  · apply BoolPoly.allRange (NatPoly.var 1)
    apply NatPoly.eqtest
    · apply NatPoly.digit
      · word_poly
      · apply code_poly <;> word_poly
      · word_poly
    · apply NatPoly.iteProp
      · word_poly
      · word_poly
      · apply NatPoly.digit
        · word_poly
        · apply code_poly <;> word_poly
        · word_poly

end NumericWL

namespace NumericKernel
open WordExpressions

theorem table_poly_of {m} {N : (Fin m → Word) → ℕ} {w : (Fin m → Word) → ℕ} {b : (Fin m → Word) → ℕ} {c : (Fin m → Word) → ℕ} {ac : (Fin m → Word) → Word} {tr : (Fin m → Word) → Word} {ini : (Fin m → Word) → Word} {r : (Fin m → Word) → ℕ}
    (h_N : NatPoly N)    (h_w : NatPoly w)    (h_b : NatPoly b)    (h_c : NatPoly c)    (h_ac : Poly ac)    (h_tr : Poly tr)    (h_ini : Poly ini)    (h_r : NatPoly r) :
    Poly (fun S => table (N S) (w S) (b S) (c S) (ac S) (tr S) (ini S) (r S)) := by
  have h := table_poly.subst (g := ![fun S => unary (N S),fun S => unary (w S),fun S => unary (b S),fun S => unary (c S),ac,tr,ini,fun S => unary (r S)])
    (by intro i; fin_cases i; exacts [h_N,h_w,h_b,h_c,h_ac,h_tr,h_ini,h_r])
  simpa [unary] using h

end NumericKernel
namespace NumericWL
open WordExpressions

theorem equalCounts_poly_of {m} {t : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (h_t : NatPoly t)    (h_W : Poly W) :
    BoolPoly (fun S => equalCounts (t S) (W S)) := by
  have h := equalCounts_poly.subst (g := ![fun S => unary (t S),W])
    (by intro i; fin_cases i; exacts [h_t,h_W])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem neighborActive_poly_of {m} {n : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word} {V : (Fin m → Word) → Word} {a : (Fin m → Word) → ℕ} {z : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_W : Poly W)    (h_V : Poly V)    (h_a : NatPoly a)    (h_z : NatPoly z) :
    BoolPoly (fun S => neighborActive (n S) (W S) (V S) (a S) (z S)) := by
  have h := neighborActive_poly.subst (g := ![fun S => unary (n S),W,V,fun S => unary (a S),fun S => unary (z S)])
    (by intro i; fin_cases i; exacts [h_n,h_W,h_V,h_a,h_z])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem neighborTrans_poly_of {m} {n : (Fin m → Word) → ℕ} {a : (Fin m → Word) → ℕ} {z : (Fin m → Word) → ℕ} {i : (Fin m → Word) → ℕ} {y : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_a : NatPoly a)    (h_z : NatPoly z)    (h_i : NatPoly i)    (h_y : NatPoly y) :
    BoolPoly (fun S => neighborTrans (n S) (a S) (z S) (i S) (y S)) := by
  have h := neighborTrans_poly.subst (g := ![fun S => unary (n S),fun S => unary (a S),fun S => unary (z S),fun S => unary (i S),fun S => unary (y S)])
    (by intro i; fin_cases i; exacts [h_n,h_a,h_z,h_i,h_y])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem tupleInitial_poly_of {m} {n : (Fin m → Word) → ℕ} {k : (Fin m → Word) → ℕ} {t : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word} {V : (Fin m → Word) → Word} {a : (Fin m → Word) → ℕ} {b : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_k : NatPoly k)    (h_t : NatPoly t)    (h_W : Poly W)    (h_V : Poly V)    (h_a : NatPoly a)    (h_b : NatPoly b) :
    BoolPoly (fun S => tupleInitial (n S) (k S) (t S) (W S) (V S) (a S) (b S)) := by
  have h := tupleInitial_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),fun S => unary (t S),W,V,fun S => unary (a S),fun S => unary (b S)])
    (by intro i; fin_cases i; exacts [h_n,h_k,h_t,h_W,h_V,h_a,h_b])
  simpa [unary] using h

end NumericWL
namespace NumericWL
open WordExpressions

theorem tupleTrans_poly_of {m} {n : (Fin m → Word) → ℕ} {k : (Fin m → Word) → ℕ} {t : (Fin m → Word) → ℕ} {a : (Fin m → Word) → ℕ} {z : (Fin m → Word) → ℕ} {i : (Fin m → Word) → ℕ} {y : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_k : NatPoly k)    (h_t : NatPoly t)    (h_a : NatPoly a)    (h_z : NatPoly z)    (h_i : NatPoly i)    (h_y : NatPoly y) :
    BoolPoly (fun S => tupleTrans (n S) (k S) (t S) (a S) (z S) (i S) (y S)) := by
  have h := tupleTrans_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),fun S => unary (t S),fun S => unary (a S),fun S => unary (z S),fun S => unary (i S),fun S => unary (y S)])
    (by intro i; fin_cases i; exacts [h_n,h_k,h_t,h_a,h_z,h_i,h_y])
  simpa [unary] using h

end NumericWL

namespace NumericGraph
open WordExpressions

theorem simple_poly_of {m} {n : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word}
    (h_n : NatPoly n)    (h_W : Poly W) :
    BoolPoly (fun S => simple (n S) (W S)) := by
  have h := simple_poly.subst (g := ![fun S => unary (n S),W])
    (by intro i; fin_cases i; exacts [h_n,h_W])
  simpa [unary] using h

end NumericGraph
namespace NumericGraph
open WordExpressions

theorem iso_poly_of {m} {n : (Fin m → Word) → ℕ} {c : (Fin m → Word) → ℕ} {W : (Fin m → Word) → Word} {V : (Fin m → Word) → Word}
    (h_n : NatPoly n)    (h_c : NatPoly c)    (h_W : Poly W)    (h_V : Poly V) :
    BoolPoly (fun S => iso (n S) (c S) (W S) (V S)) := by
  have h := iso_poly.subst (g := ![fun S => unary (n S),fun S => unary (c S),W,V])
    (by intro i; fin_cases i; exacts [h_n,h_c,h_W,h_V])
  simpa [unary] using h

end NumericGraph
namespace NumericGraph
open WordExpressions

theorem mate_poly_of {m} {n : (Fin m → Word) → ℕ} {mask : (Fin m → Word) → ℕ}
    (h_n : NatPoly n)    (h_mask : NatPoly mask) :
    Poly (fun S => mate (n S) (mask S)) := by
  have h := mate_poly.subst (g := ![fun S => unary (n S),fun S => unary (mask S)])
    (by intro i; fin_cases i; exacts [h_n,h_mask])
  simpa [unary] using h

end NumericGraph

namespace NumericWL
open WordExpressions

theorem neighborActiveTable_poly : Poly (fun S : Fin 3 → Word =>
    pairTable ((S 0).length+(S 0).length) (neighborActive (S 0).length (S 1) (S 2))) := by
  unfold pairTable
  apply Poly.tabulateRange
  · word_poly
  · apply neighborActive_poly_of <;> word_poly

theorem neighborTransTable_poly : Poly (fun S : Fin 1 → Word =>
    transTable ((S 0).length+(S 0).length) 1 (S 0).length (neighborTrans (S 0).length)) := by
  unfold transTable
  apply Poly.tabulateRange
  · word_poly
  · exact neighborTrans_poly_of (NatPoly.var 0) ((NatPoly.var 1).unpair_fst)
      ((NatPoly.var 1).unpair_snd.unpair_fst) ((NatPoly.var 1).unpair_snd.unpair_snd.unpair_fst)
      ((NatPoly.var 1).unpair_snd.unpair_snd.unpair_snd)

theorem trueTable_poly {m} {N : (Fin m → Word) → ℕ} (hN : NatPoly N) :
    Poly (fun S => pairTable (N S) (fun _ _ => true)) := by
  unfold pairTable
  exact Poly.tabulateRange (NatPoly.succ (NatPoly.pair hN hN)) (BoolPoly.const true)

theorem tupleInitialTable_poly : Poly (fun S : Fin 5 → Word =>
    pairTable ((S 2).length+(S 2).length)
      (tupleInitial (S 0).length (S 1).length (S 2).length (S 3) (S 4))) := by
  unfold pairTable
  apply Poly.tabulateRange
  · word_poly
  · apply tupleInitial_poly_of <;> word_poly

theorem tupleTransTable_poly : Poly (fun S : Fin 3 → Word =>
    transTable ((S 2).length+(S 2).length) (S 1).length (S 0).length
      (tupleTrans (S 0).length (S 1).length (S 2).length)) := by
  unfold transTable
  apply Poly.tabulateRange
  · word_poly
  · exact tupleTrans_poly_of (NatPoly.var 0) (NatPoly.var 1) (NatPoly.var 2)
      ((NatPoly.var 3).unpair_fst) ((NatPoly.var 3).unpair_snd.unpair_fst)
      ((NatPoly.var 3).unpair_snd.unpair_snd.unpair_fst) ((NatPoly.var 3).unpair_snd.unpair_snd.unpair_snd)

end NumericWL

namespace NumericWL
open WordExpressions

theorem neighborActiveTable_poly_of {m} {n : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hW : Poly W) (hV : Poly V) :
    Poly (fun S => pairTable (n S+n S) (neighborActive (n S) (W S) (V S))) := by
  have h := neighborActiveTable_poly.subst (g := ![fun S => unary (n S),W,V])
    (by intro i; fin_cases i; exacts [hn,hW,hV])
  simpa [unary] using h

theorem neighborTransTable_poly_of {m} {n : (Fin m → Word) → ℕ} (hn : NatPoly n) :
    Poly (fun S => transTable (n S+n S) 1 (n S) (neighborTrans (n S))) := by
  have h := neighborTransTable_poly.subst (g := ![fun S => unary (n S)])
    (by intro i; fin_cases i; exact hn)
  simpa [unary] using h

theorem tupleInitialTable_poly_of {m} {n k t : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (ht : NatPoly t) (hW : Poly W) (hV : Poly V) :
    Poly (fun S => pairTable (t S+t S) (tupleInitial (n S) (k S) (t S) (W S) (V S))) := by
  have h := tupleInitialTable_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),
    fun S => unary (t S),W,V]) (by intro i; fin_cases i; exacts [hn,hk,ht,hW,hV])
  simpa [unary] using h

theorem tupleTransTable_poly_of {m} {n k t : (Fin m → Word) → ℕ}
    (hn : NatPoly n) (hk : NatPoly k) (ht : NatPoly t) :
    Poly (fun S => transTable (t S+t S) (k S) (n S) (tupleTrans (n S) (k S) (t S))) := by
  have h := tupleTransTable_poly.subst (g := ![fun S => unary (n S),fun S => unary (k S),
    fun S => unary (t S)]) (by intro i; fin_cases i; exacts [hn,hk,ht])
  simpa [unary] using h

theorem neighbor_poly_of {m} {n c : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hc : NatPoly c) (hW : Poly W) (hV : Poly V) :
    BoolPoly (fun S => neighbor (n S) (c S) (W S) (V S)) := by
  exact equalCounts_poly_of hn (NumericKernel.table_poly_of (hn.add hn) (NatPoly.const 1) hn hc
    (neighborActiveTable_poly_of hn hW hV) (neighborTransTable_poly_of hn)
    (trueTable_poly (hn.add hn)) ((hn.add hn).mul (hn.add hn)))

theorem tuple_poly_of {m} {n k c : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (hc : NatPoly c) (hW : Poly W) (hV : Poly V) :
    BoolPoly (fun S => tuple (n S) (k S) (c S) (W S) (V S)) := by
  have ht := NatPoly.cappedPow hn hk hc
  exact equalCounts_poly_of ht (NumericKernel.table_poly_of (ht.add ht) hk hn hc
    (trueTable_poly (ht.add ht)) (tupleTransTable_poly_of hn hk ht)
    (tupleInitialTable_poly_of hn hk ht hW hV) ((ht.add ht).mul (ht.add ht)))

theorem equivalent_poly_of {m} {n k c : (Fin m → Word) → ℕ} {W V : (Fin m → Word) → Word}
    (hn : NatPoly n) (hk : NatPoly k) (hc : NatPoly c) (hW : Poly W) (hV : Poly V) :
    BoolPoly (fun S => equivalent (n S) (k S) (c S) (W S) (V S)) :=
  BoolPoly.iteProp (NatPoly.eqtest hk (NatPoly.const 1))
    (neighbor_poly_of hn hc hW hV) (tuple_poly_of hn hk hc hW hV)

end NumericWL

end WLIdentification

end OAI
