import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePromise

namespace OAI

/-! Size bounds for the actual binary source serialization. In particular,
the number of sites and edges is bounded by the input bit length. -/

namespace ContinuumCoulomb
open BinaryEncoding

namespace BinaryEncoding

theorem natural_length_pos (n : ℕ) : 0 < (natural.encode n).length := by
  rw [natural_length]
  omega

theorem integer_length_pos (z : ℤ) : 0 < (integer.encode z).length := by
  cases z <;> simp only [integer, List.length_cons] <;> omega

theorem list_count_le {α : Type*} (a : Codec α) (ha : ∀ x, 0 < (a.encode x).length)
    (xs : List α) : xs.length ≤ ((list a).encode xs).length := by
  have hsum : xs.length ≤ (xs.map (fun x => (a.encode x).length)).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hx := ha x
      omega
  rw [list_length]
  omega

end BinaryEncoding

theorem binaryRational_length_pos (q : BinaryRational) :
    0 < (binaryRationalCodec.encode q).length := by
  change 0 < (integer.encode q.numerator ++ natural.encode q.denominator).length
  rw [List.length_append]
  have h := integer_length_pos q.numerator
  omega

theorem binaryHeisenbergEdge_length_pos (e : BinaryHeisenbergEdge) :
    0 < (binaryHeisenbergEdgeCodec.encode e).length := by
  change 0 < (natural.encode e.left ++
    (natural.encode e.right ++ binaryRationalCodec.encode e.coefficient)).length
  simp only [List.length_append]
  have h := natural_length_pos e.left
  omega

theorem binaryHeisenberg_count_le_length (d : BinaryHeisenberg) :
    d.coordinate.length + d.edges.length ≤ (binaryHeisenbergCodec.encode d).length := by
  have hc := list_count_le (pair integer integer)
    (fun p => by rw [pair_length]; have h := integer_length_pos p.1; omega) d.coordinate
  have he := list_count_le binaryHeisenbergEdgeCodec binaryHeisenbergEdge_length_pos d.edges
  change d.coordinate.length + d.edges.length ≤
    ((BinaryEncoding.list (pair integer integer)).encode d.coordinate ++
      ((BinaryEncoding.list binaryHeisenbergEdgeCodec).encode d.edges ++
        (binaryRationalCodec.encode d.lower ++ binaryRationalCodec.encode d.upper))).length
  simp only [List.length_append]
  omega

theorem binaryHeisenberg_vertices_le_length (d : BinaryHeisenberg) (h : d.Valid) :
    (d.toSource h).vertices ≤ (binaryHeisenbergCodec.encode d).length := by
  have hs := binaryHeisenberg_count_le_length d
  change d.coordinate.length ≤ _
  omega

theorem binaryHeisenberg_edges_le_length (d : BinaryHeisenberg) (h : d.Valid) :
    (d.toSource h).edges ≤ (binaryHeisenbergCodec.encode d).length := by
  have hs := binaryHeisenberg_count_le_length d
  change d.edges.length ≤ _
  omega

/-- The promised polynomial extent holds for every actual decoded lattice site. -/
theorem binaryHeisenberg_decoded_extent (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) (i : Fin (d.toSource h).vertices) :
    |(((d.toSource h).coordinate i).1 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k ∧
      |(((d.toSource h).coordinate i).2 : ℝ)| ≤ ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k := by
  exact hp.coordinate_bound (d.coordinate.get i) (List.get_mem d.coordinate i)

end ContinuumCoulomb

end OAI
