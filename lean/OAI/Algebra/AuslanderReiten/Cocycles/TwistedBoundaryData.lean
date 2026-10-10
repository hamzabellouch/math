import OAI.Algebra.AuslanderReiten.Cocycles.CocycleCorners
import OAI.Algebra.AuslanderReiten.Cocycles.SparseParity

namespace OAI

namespace ArExplicit.CocycleData

def zSelected : TIndex → Bool
  | (false, .u) | (false, .v) | (false, .t) => true
  | (true, .e) | (true, .x) | (true, .y) | (true, .z) | (true, .u) | (true, .v) => true
  | _ => false

structure PairMonomial where
  first : TIndex
  second : TIndex
  output : TIndex
  qDegree : ℕ
  hDegree : ℕ
  deriving DecidableEq

def PairMonomial.number (p : PairMonomial) : ℕ :=
  p.first.number + 20 * (p.second.number + 20 * (p.output.number + 20 * (p.qDegree + 8 * p.hDegree)))

def boundaryLeftContribution (p : TripleMonomial) (m : MulMonomial) : List PairMonomial :=
  if m.first = p.output ∧ m.second = p.third.star then
    [⟨p.first, p.second, m.output, p.degree + m.degree, p.third.weight⟩] else []

def boundaryRightContributions (m : MulMonomial) : List PairMonomial :=
  (if zSelected m.second then [⟨m.first, m.second, m.output, m.degree + 1, 1⟩] else []) ++
  (if zSelected m.output then [⟨m.first, m.second, m.output, m.degree + 1, 1⟩] else []) ++
  (if zSelected m.first then [⟨m.first, m.second, m.output, m.degree + 1,
    if m.second.1 then 0 else 1⟩] else [])

def boundaryTerms : List PairMonomial :=
  (cochain.flatMap fun p => multiplication.flatMap (boundaryLeftContribution p)) ++
    multiplication.flatMap boundaryRightContributions

theorem boundary_certificate :
    SparseParity.paired (SparseParity.sort (fun x y => decide (x.number ≤ y.number)) boundaryTerms) = true := by
  decide +kernel

theorem boundaryTerms_sum_zero {M : Type*} [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : PairMonomial → M) :
    (boundaryTerms.map f).sum = 0 :=
  SparseParity.sum_eq_zero_of_sorted_paired hchar f _ _ boundary_certificate

end ArExplicit.CocycleData

end OAI
