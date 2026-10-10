import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumVerifier
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceSpectrum
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

namespace OAI

/-! Finite binary input and promise language for the published signed,
field-free square-lattice Heisenberg problem. Invalid encodings and inputs
outside the energy promise belong to neither promise set. -/

namespace ContinuumCoulomb
open BinaryEncoding

structure BinaryRational where
  numerator : ℤ
  denominator : ℕ
  deriving DecidableEq, Repr

def BinaryRational.value (q : BinaryRational) : ℚ :=
  (q.numerator : ℚ) / q.denominator

def binaryRationalEquiv : BinaryRational ≃ (ℤ × ℕ) where
  toFun q := (q.numerator, q.denominator)
  invFun q := ⟨q.1, q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

def binaryRationalCodec : Codec BinaryRational := BinaryEncoding.equiv (pair integer natural) binaryRationalEquiv

def BinaryRational.ofRat (q : ℚ) : BinaryRational := ⟨q.num, q.den⟩

@[simp] theorem BinaryRational.value_ofRat (q : ℚ) : (BinaryRational.ofRat q).value = q := by
  exact Rat.num_div_den q

structure BinaryHeisenbergEdge where
  left : ℕ
  right : ℕ
  coefficient : BinaryRational
  deriving DecidableEq, Repr

def binaryHeisenbergEdgeEquiv : BinaryHeisenbergEdge ≃ (ℕ × (ℕ × BinaryRational)) where
  toFun e := (e.left, e.right, e.coefficient)
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨i, j, q⟩; rfl

def binaryHeisenbergEdgeCodec : Codec BinaryHeisenbergEdge := BinaryEncoding.equiv
  (pair natural (pair natural binaryRationalCodec)) binaryHeisenbergEdgeEquiv

structure BinaryHeisenberg where
  coordinate : List (ℤ × ℤ)
  edges : List BinaryHeisenbergEdge
  lower : BinaryRational
  upper : BinaryRational
  deriving DecidableEq, Repr

def binaryHeisenbergEquiv : BinaryHeisenberg ≃
    (List (ℤ × ℤ) × (List BinaryHeisenbergEdge × (BinaryRational × BinaryRational))) where
  toFun d := (d.coordinate, d.edges, d.lower, d.upper)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨cs, es, a, b⟩; rfl

def binaryHeisenbergCodec : Codec BinaryHeisenberg := BinaryEncoding.equiv
  (pair (BinaryEncoding.list (pair integer integer))
    (pair (BinaryEncoding.list binaryHeisenbergEdgeCodec) (pair binaryRationalCodec binaryRationalCodec)))
      binaryHeisenbergEquiv

structure BinaryHeisenberg.Valid (d : BinaryHeisenberg) : Prop where
  vertices_pos : 0 < d.coordinate.length
  coordinate_nodup : d.coordinate.Nodup
  bounds : ∀ e : Fin d.edges.length,
    (d.edges.get e).left < d.coordinate.length ∧ (d.edges.get e).right < d.coordinate.length
  denominators : ∀ e : Fin d.edges.length, 0 < (d.edges.get e).coefficient.denominator
  adjacent : ∀ e : Fin d.edges.length,
    Int.natAbs ((d.coordinate.getD (d.edges.get e).left (0, 0)).1 -
      (d.coordinate.getD (d.edges.get e).right (0, 0)).1) +
    Int.natAbs ((d.coordinate.getD (d.edges.get e).left (0, 0)).2 -
      (d.coordinate.getD (d.edges.get e).right (0, 0)).2) = 1
  simple : ∀ e f : Fin d.edges.length, e ≠ f →
    ¬((d.edges.get e).left = (d.edges.get f).left ∧ (d.edges.get e).right = (d.edges.get f).right) ∧
    ¬((d.edges.get e).left = (d.edges.get f).right ∧ (d.edges.get e).right = (d.edges.get f).left)
  lower_denominator : 0 < d.lower.denominator
  upper_denominator : 0 < d.upper.denominator
  gap : d.lower.value < d.upper.value

/-- Decode valid finite data into the existing actual spin Hamiltonian. -/
def BinaryHeisenberg.toSource (d : BinaryHeisenberg) (h : d.Valid) : SquareLatticeHeisenberg where
  vertices := d.coordinate.length
  vertices_pos := h.vertices_pos
  coordinate := d.coordinate.get
  coordinate_injective := h.coordinate_nodup.injective_get
  edges := d.edges.length
  left e := ⟨(d.edges.get e).left, (h.bounds e).1⟩
  right e := ⟨(d.edges.get e).right, (h.bounds e).2⟩
  adjacent e := by
    have ha := h.adjacent e
    rw [List.getD_eq_get d.coordinate (0, 0) ⟨(d.edges.get e).left, (h.bounds e).1⟩,
      List.getD_eq_get d.coordinate (0, 0) ⟨(d.edges.get e).right, (h.bounds e).2⟩] at ha
    exact ha
  edge_simple e f hne := by
    have hs := h.simple e f hne
    constructor
    · rintro ⟨hl, hr⟩
      exact hs.1 ⟨congrArg Fin.val hl, congrArg Fin.val hr⟩
    · rintro ⟨hl, hr⟩
      exact hs.2 ⟨congrArg Fin.val hl, congrArg Fin.val hr⟩
  coefficient e := (d.edges.get e).coefficient.value
  lower := d.lower.value
  upper := d.upper.value
  gap_pos := h.gap

/-- A single fixed exponent bounds lattice extent, source weights and inverse
gap, as in the polynomial-weight spatially sparse source branch. -/
structure BinaryHeisenberg.PolynomialPromise (k : ℕ) (d : BinaryHeisenberg) : Prop where
  coordinate_bound : ∀ p ∈ d.coordinate,
    |(p.1 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k ∧
      |(p.2 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k
  weight_bound : ∀ e : Fin d.edges.length, |((d.edges.get e).coefficient.value : ℝ)| ≤
    ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k
  gap_bound : (((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k)⁻¹ ≤
    (d.upper.value : ℝ) - d.lower.value

noncomputable section

def sourceHeisenbergPromise (k : ℕ) : PromiseProblem BinaryHeisenberg where
  yes := {d | ∃ h : d.Valid, d.PolynomialPromise k ∧
    sourceGroundEnergy (d.toSource h) ≤ ((d.lower.value : ℝ) : EReal)}
  no := {d | ∃ h : d.Valid, d.PolynomialPromise k ∧
    ((d.upper.value : ℝ) : EReal) ≤ sourceGroundEnergy (d.toSource h)}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro d ⟨h, _, hyes⟩ ⟨h', _, hno⟩
    have hab : ((d.upper.value : ℝ) : EReal) ≤ ((d.lower.value : ℝ) : EReal) := hno.trans hyes
    have hgap : ((d.lower.value : ℝ) : EReal) < ((d.upper.value : ℝ) : EReal) := by
      exact_mod_cast h.gap
    exact (not_le_of_gt hgap) hab

/-- Field-free signed square-lattice Heisenberg hardness of
Cubitt–Montanaro–Piddock, arXiv:1701.05182v4, Theorem 48 and Section 10.1,
with the polynomial-weight sparse construction of Lemma 47. -/
def PublishedCMPHardness : Prop :=
  ∃ k : ℕ, 0 < k ∧ QMAHard binaryHeisenbergCodec.encode (sourceHeisenbergPromise k)

end
end ContinuumCoulomb

end OAI
