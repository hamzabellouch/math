import OAI.Combinatorics.PerfectMatching.Model

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

open scoped BigOperators

namespace LoopMatching

structure LoopRecord where
  vertex : ℕ
  multiplicity : ℕ
  deriving DecidableEq

structure Input where
  ordinary : BinaryMatching.Input
  loops : List LoopRecord
  valid : ∀ e ∈ loops, e.vertex < ordinary.n
  unique : (loops.map LoopRecord.vertex).Nodup

abbrev Input.n (G : Input) : ℕ := G.ordinary.n

def loopMultiplicity (G : Input) (v : Fin G.n) : ℕ :=
  match G.loops.find? (fun r => r.vertex == v.val) with
  | none => 0
  | some r => r.multiplicity

def IsPartialMatching (n : ℕ) (M : Finset (BinaryMatching.Pair n)) : Prop :=
  ∀ v : Fin n, ∀ e ∈ M, ∀ f ∈ M,
    (BinaryMatching.completeGraph n).Incident v e →
    (BinaryMatching.completeGraph n).Incident v f → e = f

abbrev PartialMatching (n : ℕ) :=
  { M : Finset (BinaryMatching.Pair n) // IsPartialMatching n M }

noncomputable instance partialMatchingFintype (n : ℕ) : Fintype (PartialMatching n) :=
  Fintype.ofFinite _

noncomputable def loopVertices {n : ℕ} (M : PartialMatching n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v =>
    ∀ e ∈ M.val, ¬ (BinaryMatching.completeGraph n).Incident v e)

noncomputable def weight (G : Input) (M : PartialMatching G.n) : ℕ :=
  (∏ e ∈ M.val, BinaryMatching.multiplicity G.ordinary e) *
    ∏ v ∈ loopVertices M, loopMultiplicity G v

noncomputable def count (G : Input) : ℕ := ∑ M : PartialMatching G.n, weight G M

noncomputable def countWithLoops (G : Input) (j : ℕ) : ℕ := by
  classical
  exact ∑ M : PartialMatching G.n,
    if (loopVertices M).card = j then weight G M else 0

def encodeLoopRecord (r : LoopRecord) : List Bool :=
  BinaryMatching.encodeNat r.vertex ++ BinaryMatching.encodeNat r.multiplicity

def encodeInput (G : Input) : List Bool :=
  BinaryMatching.encodeInput G.ordinary ++
    BinaryMatching.encodeNat G.loops.length ++ G.loops.flatMap encodeLoopRecord

def encodeOutput (a : ℕ × ℕ) : List Bool :=
  BinaryMatching.encodeNat a.1 ++ BinaryMatching.encodeNat a.2

def outputValue (a : ℕ × ℕ) : ℚ := (a.1 : ℚ) / a.2

def FullEndpoint : Prop :=
  ∃ A : Input → ℕ × ℕ,
    ∃ machine : Turing.TM2ComputableInPolyTime encodeInput encodeOutput A,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      (∃ P : Polynomial ℕ, ∀ G,
        (encodeOutput (A G)).length ≤ P.eval (encodeInput G).length) ∧
      ∀ G, 0 < (A G).2 ∧
        (A G).1 ≤ (A G).2 * count G ∧
        (A G).2 * count G ≤ 2 ^ (18 * G.n) * (A G).1 ∧
        ((A G).1 = 0 ↔ count G = 0)

end LoopMatching

end OAI
