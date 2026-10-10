import Mathlib
import OAI.Combinatorics.KMedian.PCP.LocalReduction

namespace OAI

section Inline_PCPQueries

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

structure FourQuery (P : Type) where
  address : Fin 4 → P
  accept : BitVector (Fin 4) → Bool

namespace FourQuery
variable {P : Type}
def Rejects (q : FourQuery P) (a : P → Bit) : Prop := q.accept (a ∘ q.address) ≠ true
end FourQuery

theorem testRate_pi_eval {I : Type} [Fintype I] [DecidableEq I]
    (S : I → Type) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (i : I) (p : S i → Prop) :
    testRate (fun s : (i : I) → S i => p (s i)) = testRate p := by
  classical
  calc
    _ = testRate (fun s : S i × ((j : {j // j ≠ i}) → S j.val) => p s.1) :=
      testRate_equiv (Equiv.piSplitAt i S) (fun s => p s.1)
    _ = _ := testRate_fst p

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]
variable (R : Relation K) [DecidablePred (· ∈ R)]

abbrev LocalPosition := BitVector (Vars R) ⊕
  (BitVector (Vars R × Vars R) ⊕ (Fin 2 × BitVector K))

def firstPos (x : BitVector (Vars R)) : LocalPosition R := .inl x
def secondPos (x : BitVector (Vars R × Vars R)) : LocalPosition R := .inr (.inl x)
def leftPos (x : BitVector K) : LocalPosition R := .inr (.inr (0,x))
def rightPos (x : BitVector K) : LocalPosition R := .inr (.inr (1,x))

def assignment (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    LocalPosition R → Bit
  | .inl x => f x
  | .inr (.inl x) => h x
  | .inr (.inr (b,x)) => if b = 0 then u x else v x

abbrev Sample : Fin 6 → Type
  | 0 => BitVector (Vars R) × BitVector (Vars R)
  | 1 => BitVector (Vars R × Vars R) × BitVector (Vars R × Vars R)
  | 2 => (BitVector (Vars R) × BitVector (Vars R)) × BitVector (Vars R × Vars R)
  | 3 => BitVector (Eqs R) × BitVector (Vars R × Vars R)
  | 4 => BitVector K × BitVector (Vars R)
  | 5 => BitVector K × BitVector (Vars R)

instance sampleFintype (i : Fin 6) : Fintype (Sample R i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
instance sampleNonempty (i : Fin 6) : Nonempty (Sample R i) := by
  fin_cases i <;> dsimp [Sample] <;> infer_instance

def query : (i : Fin 6) → Sample R i → FourQuery (LocalPosition R)
  | 0, (x,y) => ⟨![firstPos R (x+y), firstPos R x, firstPos R y, firstPos R x],
      fun z => decide (z 0 = z 1 + z 2)⟩
  | 1, (x,y) => ⟨![secondPos R (x+y), secondPos R x, secondPos R y, secondPos R x],
      fun z => decide (z 0 = z 1 + z 2)⟩
  | 2, ((x,y),z) => ⟨![firstPos R x, firstPos R y,
      secondPos R (tensor x y + z), secondPos R z],
      fun w => decide (w 0 * w 1 = w 2 - w 3)⟩
  | 3, (t,z) => ⟨![secondPos R ((quadratic R).combination t + z),
      secondPos R z, secondPos R z, secondPos R z],
      fun w => decide (w 0 - w 1 = dot (quadratic R).rhs t)⟩
  | 4, (x,z) => ⟨![firstPos R (liftQuery (leftEmbed R) x + z),
      firstPos R z, leftPos R x, leftPos R x],
      fun w => decide (w 0 - w 1 = w 2)⟩
  | 5, (x,z) => ⟨![firstPos R (liftQuery (rightEmbed R) x + z),
      firstPos R z, rightPos R x, rightPos R x],
      fun w => decide (w 0 - w 1 = w 2)⟩

abbrev Pad := (i : Fin 6) → Sample R i

def packed (s : Fin 6 × Pad R) : FourQuery (LocalPosition R) := query R s.1 (s.2 s.1)

theorem packed_rate (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    testRate (fun s => (packed R s).Rejects (assignment R f h u v)) =
      rejectionWeight R f h u v / 6 := by
  classical
  change testRate (fun s : Fin 6 × Pad R =>
    (query R s.1 (s.2 s.1)).Rejects (assignment R f h u v)) = _
  rw [testRate_prod (S := Fin 6) (T := Pad R)
    (fun (i : Fin 6) (s : Pad R) => (query R i (s i)).Rejects (assignment R f h u v))]
  have hm (i : Fin 6) :
      testRate (fun s : Pad R => (query R i (s i)).Rejects (assignment R f h u v)) =
      testRate (fun s : Sample R i => (query R i s).Rejects (assignment R f h u v)) :=
    testRate_pi_eval (Sample R) i
      (fun s : Sample R i => (query R i s).Rejects (assignment R f h u v))
  change (𝔼 i, testRate (fun s : Pad R =>
    (query R i (s i)).Rejects (assignment R f h u v))) = _
  simp_rw [hm]
  rw [Fintype.expect_eq_sum_div_card]
  norm_num only [Fintype.card_fin, Fin.sum_univ_succ, Fin.reduceSucc,
    Finset.sum_empty, add_zero]
  congr 1
  simp only [query, FourQuery.Rejects, firstPos, secondPos, leftPos, rightPos,
    rejectionWeight, QuadraticSystem.rejectionWeight,
    linearityRate, multiplicationRate, QuadraticSystem.equationRate,
    boundaryRate, derivative, add_assoc]
  simp only [Function.comp_def]
  simp only [assignment, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  simp only [Bool.not_eq_true]
  simp
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply testRate_congr
    intro s
    exact decide_eq_false_iff_not
  · apply congrArg₂ (fun x y : ℝ => x + y)
    · apply testRate_congr
      intro s
      exact decide_eq_false_iff_not
    · apply congrArg₂ (fun x y : ℝ => x + y)
      · apply testRate_congr
        intro s
        exact decide_eq_false_iff_not
      · apply congrArg₂ (fun x y : ℝ => x + y)
        · apply testRate_congr
          intro s
          exact decide_eq_false_iff_not
        · rfl

theorem packed_sound (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
    (hR : (nearestLabel u, nearestLabel v) ∉ R) :
    1/96 ≤ testRate (fun s => (packed R s).Rejects (assignment R f h u v)) := by
  rw [packed_rate]
  have hh := sound R f h u v hR
  linarith

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPQueries

end OAI
