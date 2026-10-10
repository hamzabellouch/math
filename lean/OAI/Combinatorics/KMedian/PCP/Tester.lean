import Mathlib
import OAI.Combinatorics.KMedian.PCP.Quadratic

namespace OAI

section Inline_PCPTester

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def QuadraticSystem.rejectionWeight (Q : QuadraticSystem V E)
    (f : BitVector V → Bit) (h : BitVector (V × V) → Bit) : ℝ :=
  linearityRate f + linearityRate h + multiplicationRate f h + Q.equationRate h

theorem multiplication_exact (f : BitVector V →+ Bit) (h : BitVector (V × V) →+ Bit)
    (hr : testRate (fun p : BitVector V × BitVector V =>
      f p.1 * f p.2 ≠ h (tensor p.1 p.2)) < 1/4) :
    ∀ x y, h (tensor x y) = f x * f y := by
  intro x y
  by_contra hm
  have hn : multiplicationDiscrepancy f f h x y ≠ 0 := sub_ne_zero.mpr hm
  have hb := bilinear_nonzero_rate (multiplicationDiscrepancy f f h) x y hn
  have he : testRate (fun p : BitVector V × BitVector V =>
      multiplicationDiscrepancy f f h p.1 p.2 ≠ 0) =
      testRate (fun p : BitVector V × BitVector V =>
      f p.1 * f p.2 ≠ h (tensor p.1 p.2)) := by
    apply testRate_congr
    intro p
    change (h (tensor p.1 p.2) - f p.1 * f p.2 ≠ 0) ↔ _
    exact sub_ne_zero.trans ne_comm
  rw [he] at hb
  linarith

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

theorem decode (f : BitVector V → Bit) (h : BitVector (V × V) → Bit)
    (hr : Q.rejectionWeight f h < 1/16) :
    ∃ a : BitVector V, Q.Satisfies a ∧
      testRate (fun x => f x ≠ dot a x) ≤ 2 * linearityRate f := by
  have hn₁ : 0 ≤ linearityRate f := testRate_nonneg _
  have hn₂ : 0 ≤ linearityRate h := testRate_nonneg _
  have hn₃ : 0 ≤ multiplicationRate f h := testRate_nonneg _
  have hn₄ : 0 ≤ Q.equationRate h := testRate_nonneg _
  have hsum : linearityRate f + linearityRate h + multiplicationRate f h +
      Q.equationRate h < 1/16 := hr
  have hf : linearityRate f < 1/6 := by linarith only [hsum, hn₂, hn₃, hn₄]
  have hh : linearityRate h < 1/6 := by linarith only [hsum, hn₁, hn₃, hn₄]
  let F := correctedHom f (linearityRate_small f hf)
  let H := correctedHom h (linearityRate_small h hh)
  have hmul : ∀ x y, H (tensor x y) = F x * F y := by
    apply multiplication_exact F H
    have hb := multiplication_transfer f h hf
    change testRate (fun p : BitVector V × BitVector V =>
      corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2)) < 1/4
    linarith only [hb, hsum, hn₁, hn₂, hn₃, hn₄]
  have heq : ∀ e, H (Q.form e) = Q.rhs e := by
    apply Q.equation_exact H
    have hb := Q.equation_transfer h
    change testRate (fun t => corrected h (Q.combination t) ≠ dot Q.rhs t) < 1/2
    linarith only [hb, hsum, hn₁, hn₂, hn₃, hn₄]
  have hcoords := multiplication_identifies_tensor F F H hmul
  refine ⟨coordinates F, ?_, ?_⟩
  · intro e
    rw [← hcoords, ← linear_representation]
    exact heq e
  · have hd := corrected_distance f hf
    have he : (fun x => dot (coordinates F) x) = corrected f := by
      funext x
      exact (linear_representation F x).symm
    simpa only [he] using hd

theorem sound (hQ : ¬ ∃ a, Q.Satisfies a) (f : BitVector V → Bit)
    (h : BitVector (V × V) → Bit) : 1/16 ≤ Q.rejectionWeight f h := by
  by_contra hr
  obtain ⟨a,ha,_⟩ := Q.decode f h (lt_of_not_ge hr)
  exact hQ ⟨a,ha⟩

@[simp] theorem derivative_hom {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (g : G →+ H) (x y : G) : derivative g x y = g x := by
  simp [derivative]

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem dot_combination (a : BitVector (V × V)) (t : BitVector E) :
    dot a (Q.combination t) = ∑ e, t e * dot a (Q.form e) := by
  change (dotHom a) (∑ e, t e • Q.form e) = _
  rw [map_sum]
  apply sum_congr rfl
  intro e _
  rw [ZMod.map_smul]
  rfl

theorem complete (a : BitVector V) (ha : Q.Satisfies a) :
    Q.rejectionWeight (dot a) (dot (tensor a a)) = 0 := by
  have hf : linearityRate (dot a) = 0 := by
    convert testRate_false (S := BitVector V × BitVector V) using 1
    apply testRate_congr
    intro p
    simp [dot_add_right]
  have hh : linearityRate (dot (tensor a a)) = 0 := by
    convert testRate_false (S := BitVector (V × V) × BitVector (V × V)) using 1
    apply testRate_congr
    intro p
    simp [dot_add_right]
  have hm : multiplicationRate (dot a) (dot (tensor a a)) = 0 := by
    convert testRate_false (S := (BitVector V × BitVector V) × BitVector (V × V)) using 1
    apply testRate_congr
    intro p
    simp [derivative, dot_add_right, dot_tensor]
  have he : Q.equationRate (dot (tensor a a)) = 0 := by
    convert testRate_false (S := BitVector E × BitVector (V × V)) using 1
    apply testRate_congr
    intro p
    have heach : dot (tensor a a) (Q.combination p.1) = dot Q.rhs p.1 := by
      rw [Q.dot_combination]
      change (∑ e, p.1 e * dot (tensor a a) (Q.form e)) = ∑ e, Q.rhs e * p.1 e
      apply sum_congr rfl
      intro e _
      rw [ha e, mul_comm]
    simp [derivative, dot_add_right, heach]
  simp only [rejectionWeight, hf, hh, hm, he, add_zero]
end QuadraticSystem
end MetricKMedian.PCP

end Inline_PCPTester

end OAI
