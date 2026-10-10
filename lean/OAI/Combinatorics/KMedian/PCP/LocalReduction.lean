import Mathlib
import OAI.Combinatorics.KMedian.PCP.Boundary
import OAI.Combinatorics.KMedian.PCP.Tester

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

abbrev Relation (K : Type) := Set (BitVector K × BitVector K)

variable (R : Relation K) [DecidablePred (· ∈ R)]

abbrev Allowed := {p : BitVector K × BitVector K // p ∈ R}
abbrev Vars := RelationEncoding.Variable (K ⊕ K) (Allowed R)
abbrev Eqs := RelationEncoding.Equation (K ⊕ K) (Allowed R)

instance : DecidableEq (Vars R) := by
  letI : DecidableEq (Allowed R) := inferInstance
  infer_instance
instance : DecidableEq (Eqs R) := by
  letI : DecidableEq (Allowed R) := inferInstance
  infer_instance

def label (p : Allowed R) : BitVector (K ⊕ K) := Sum.elim p.val.1 p.val.2

def quadratic : QuadraticSystem (Vars R) (Eqs R) := RelationEncoding.system (label R)

def leftEmbed (i : K) : Vars R := .inl (.inl i)
def rightEmbed (i : K) : Vars R := .inl (.inr i)

noncomputable def rejectionWeight (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) : ℝ :=
  (quadratic R).rejectionWeight f h +
    boundaryRate (leftEmbed R) f u + boundaryRate (rightEmbed R) f v

theorem rejectionWeight_nonneg (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    0 ≤ rejectionWeight R f h u v := by
  unfold rejectionWeight QuadraticSystem.rejectionWeight
  exact add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (add_nonneg (testRate_nonneg _) (testRate_nonneg _))
      (testRate_nonneg _)) (testRate_nonneg _)) (testRate_nonneg _)) (testRate_nonneg _)

theorem decode (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
    (hr : rejectionWeight R f h u v < 1/16) :
    (nearestLabel u, nearestLabel v) ∈ R := by
  have n₁ : 0 ≤ linearityRate f := testRate_nonneg _
  have n₂ : 0 ≤ linearityRate h := testRate_nonneg _
  have n₃ : 0 ≤ multiplicationRate f h := testRate_nonneg _
  have n₄ : 0 ≤ (quadratic R).equationRate h := testRate_nonneg _
  have nL : 0 ≤ boundaryRate (leftEmbed R) f u := testRate_nonneg _
  have nR : 0 ≤ boundaryRate (rightEmbed R) f v := testRate_nonneg _
  have hsum : linearityRate f + linearityRate h + multiplicationRate f h +
      (quadratic R).equationRate h + boundaryRate (leftEmbed R) f u +
      boundaryRate (rightEmbed R) f v < 1/16 := hr
  have hquad : (quadratic R).rejectionWeight f h < 1/16 := by
    change linearityRate f + linearityRate h + multiplicationRate f h +
      (quadratic R).equationRate h < 1/16
    linarith only [hsum, nL, nR]
  obtain ⟨a,ha,hd⟩ := (quadratic R).decode f h hquad
  obtain ⟨p,hp⟩ := RelationEncoding.sound (label R) a ha
  have hleft : a ∘ leftEmbed R = p.val.1 := funext (fun i => hp (.inl i))
  have hright : a ∘ rightEmbed R = p.val.2 := funext (fun i => hp (.inr i))
  have hL : p.val.1 = nearestLabel u := by
    by_contra hL
    have hy := nearestLabel_robust u p.val.1 hL
    have hx := boundary_transfer (leftEmbed R) f u a
    rw [hleft] at hx
    linarith only [hy, hx, hd, hsum, n₁, n₂, n₃, n₄, nL, nR]
  have hR : p.val.2 = nearestLabel v := by
    by_contra hR
    have hy := nearestLabel_robust v p.val.2 hR
    have hx := boundary_transfer (rightEmbed R) f v a
    rw [hright] at hx
    linarith only [hy, hx, hd, hsum, n₁, n₂, n₃, n₄, nL, nR]
  have hpR : (p.val.1, p.val.2) ∈ R := p.property
  simpa only [hL, hR] using hpR

theorem sound (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
    (hR : (nearestLabel u, nearestLabel v) ∉ R) :
    1/16 ≤ rejectionWeight R f h u v := by
  by_contra hr
  exact hR (decode R f h u v (lt_of_not_ge hr))

theorem complete (p : Allowed R) :
    ∃ f h, rejectionWeight R f h (dot p.val.1) (dot p.val.2) = 0 := by
  let a := RelationEncoding.witness (label R) p
  let f := dot a
  let h := dot (tensor a a)
  have ha : (quadratic R).Satisfies a := RelationEncoding.complete (label R) p
  have hq := (quadratic R).complete a ha
  have hleft : a ∘ leftEmbed R = p.val.1 := rfl
  have hright : a ∘ rightEmbed R = p.val.2 := rfl
  have hl : boundaryRate (leftEmbed R) f (dot p.val.1) = 0 := by
    unfold boundaryRate
    convert testRate_false (S := BitVector K × BitVector (Vars R)) using 1
    apply testRate_congr
    intro q
    simp [f, derivative, dot_add_right, dot_liftQuery, hleft]
  have hr : boundaryRate (rightEmbed R) f (dot p.val.2) = 0 := by
    unfold boundaryRate
    convert testRate_false (S := BitVector K × BitVector (Vars R)) using 1
    apply testRate_congr
    intro q
    simp [f, derivative, dot_add_right, dot_liftQuery, hright]
  refine ⟨f,h,?_⟩
  change (quadratic R).rejectionWeight (dot a) (dot (tensor a a)) + _ + _ = 0
  rw [hq, hl, hr]
  norm_num
end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
