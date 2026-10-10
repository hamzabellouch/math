import OAI.Computability.SpaceSimulation.Epoch.Core
import OAI.Computability.SpaceSimulation.Evaluation.Circuit

namespace OAI

/-! Lay out the implicit word graph in flat (epoch,column) order. -/
namespace Fifths
namespace Tour
open Radix Bin Circuit
variable (D : Tour)

/-- First N array columns, then start and k round history columns. -/
def stride := D.N+D.k+1
def total := D.E*D.stride
abbrev Vertex := Fin D.total
theorem stride_pos : 0 < D.stride := Nat.zero_lt_succ _
theorem total_pos : 0 < D.total := Nat.mul_pos (Nat.zero_lt_succ _) D.stride_pos

def epoch (v : D.Vertex) := v.val / D.stride
def col (v : D.Vertex) := v.val % D.stride
def mkV (e j : ℕ) : D.Vertex :=
  ⟨(e*D.stride + j) % D.total,Nat.mod_lt _ D.total_pos⟩
def hV (e j : ℕ) := D.mkV e (D.N+j)

theorem epoch_lt (v : D.Vertex) : D.epoch v < D.E :=
  (Nat.div_lt_iff_lt_mul D.stride_pos).mpr v.isLt
theorem col_lt (v : D.Vertex) : D.col v < D.stride := Nat.mod_lt _ D.stride_pos
theorem re_V (v : D.Vertex) : D.mkV (D.epoch v) (D.col v) = v := by
  apply Fin.ext
  have e := Nat.mod_add_div v.val D.stride
  unfold mkV epoch col
  dsimp
  rw [mul_comm,add_comm,e,Nat.mod_eq_of_lt v.isLt]
theorem mkV_val {e j : ℕ} (p : e<D.E) (h : j < D.stride) :
    (D.mkV e j).val = e*D.stride+j := by
  unfold mkV; dsimp
  apply Nat.mod_eq_of_lt
  unfold total
  nlinarith only [p,h,Nat.zero_le e,D.stride_pos]
theorem epoch_v {e j : ℕ} (p : e < D.E) (h : j < D.stride) :
    D.epoch (D.mkV e j) = e := by
  unfold epoch
  rw [D.mkV_val p h, add_comm, mul_comm,Nat.add_mul_div_left]
  · rw [Nat.div_eq_of_lt h,Nat.zero_add]
  · exact D.stride_pos
theorem col_v {e j : ℕ} (p : e < D.E) (h : j < D.stride) :
    D.col (D.mkV e j) = j := by
  unfold col
  rw [D.mkV_val p h,add_comm]
  simp [Nat.mod_eq_of_lt h]

/-- Round index 0 on array columns too, so all calls can parse
their local functions in uniform space regardless of type. -/
def round (v : D.Vertex) := D.col v - D.N
theorem round_le (v : D.Vertex) : D.round v ≤ D.k := by
  have h := D.col_lt v
  unfold round
  unfold stride at h
  omega

def valueOf (v : D.Vertex) :=
  let e := D.epoch v * D.b
  if D.col v < D.N then (D.story e).cells (D.col v)
  else D.log e (D.round v*D.k)
def firstOf (v : D.Vertex) :=
  if D.col v < D.N then D.tape (D.col v) else D.init

def baseOf (v : D.Vertex) :=
  decide (D.epoch v = 0) && decide (D.col v ≤ D.N)
def guesses (v : D.Vertex) :=
  if D.col v ≤ D.N then 0 else D.guessLength

def header (v : D.Vertex) :=
  if D.col v ≤ D.N then D.hV (D.epoch v - 1) D.k
  else D.hV (D.epoch v) (D.round v - 1)
def childrenOf (v : D.Vertex) (i : ℕ) :=
  if D.col v < D.N then D.mkV (D.epoch v - 1) (D.col v)
  else if D.col v = D.N then D.header v
  else D.mkV (D.epoch v) i

def proposal (v : D.Vertex) (h y : ℕ) :=
  let n := (D.round v-1)*D.k + 1
  h % D.m^n + D.m^n*y -- `y` full guess (possibly invalid at local-only inputs)

def offer (v : D.Vertex) (z y h : ℕ) :=
  if D.col v < D.N then 1
  else if D.col v = D.N then Modulus.augBit D.width (get D.m h D.b) z
  else Modulus.augBit D.width (D.proposal v h y) z

def validAt (v : D.Vertex) (z y i h a : ℕ) :=
  if D.col v < D.N then
    if i = 0 then
      Modulus.augBit D.width (D.replay (D.col v) h a D.b).1 z
    else 1
  else if D.col v = D.N then 1
  else (D.replay i (D.proposal v h y) a (D.round v*D.k)).2.toNat

def circuit : Circuit where
  width := D.width
  count := D.N
  nodes := D.total
  base := D.baseOf
  head := D.header
  child := D.childrenOf
  guessing := D.guesses
  first := D.firstOf
  propose := D.offer
  allows := D.validAt
  semantic := D.valueOf

def target : D.Vertex := D.hV (D.E-1) D.k
-- meter values
def coinsEasy := D.circuit.price 0
def coinsHard := D.circuit.price D.guessLength
def per := D.coinsHard + (D.k+2) * D.coinsEasy
def coins (v : D.Vertex) :=
  let a := D.epoch v * D.per
  if D.col v < D.N then a
  else a + D.coinsHard + (D.round v+1)*D.coinsEasy

-- flat-coordinates API
theorem hc {e j} (p : e < D.E) (h : j ≤ D.k) :
    D.col (D.hV e j) = D.N+j := D.col_v p (by unfold stride; omega)
theorem he {e j} (p : e < D.E) (h : j ≤ D.k) :
    D.epoch (D.hV e j) = e := D.epoch_v p (by unfold stride; omega)
theorem hr {e j} (p : e < D.E) (h : j ≤ D.k) :
    D.round (D.hV e j) = j := by rw [round,D.hc p h]; omega
theorem ac {e j} (p : e < D.E) (h : j < D.N) :
    D.col (D.mkV e j) = j := D.col_v p (lt_of_lt_of_le h (by unfold stride; omega))
theorem ae {e j} (p : e < D.E) (h : j < D.N) :
    D.epoch (D.mkV e j) = e := D.epoch_v p (lt_of_lt_of_le h (by unfold stride; omega))
theorem at_array {e i} (h : e < D.E) (g : i < D.N) :
    D.valueOf (D.mkV e i) = (D.story (e*D.b)).cells i := by
  simp only [valueOf,D.ae h g,D.ac h g,g,↓reduceIte]
theorem at_history {e j} (h : e < D.E) (g : j ≤ D.k) :
    D.valueOf (D.hV e j) = D.log (e*D.b) (j*D.k) := by
  simp only [valueOf,D.he h g,D.hc h g,D.hr h g,show ¬ D.N+j<D.N by omega,↓reduceIte]

/-- Useful for correctness proofs. -/
theorem either (v : D.Vertex) :
    (∃ e < D.E, ∃ j < D.N, v = D.mkV e j) ∨
    (∃ e < D.E, ∃ j ≤ D.k, v = D.hV e j) := by
  by_cases h : D.col v < D.N
  · exact .inl ⟨D.epoch v,D.epoch_lt v,D.col v,h,(D.re_V v).symm⟩
  · refine .inr ⟨D.epoch v,D.epoch_lt v,D.round v,D.round_le v,?_⟩
    unfold hV round
    rw [show D.N+(D.col v-D.N) = D.col v by omega]
    exact (D.re_V v).symm
end Tour
end Fifths

end OAI
