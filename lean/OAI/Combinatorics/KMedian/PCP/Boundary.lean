import Mathlib
import OAI.Combinatorics.KMedian.PCP.QuadraticEncoding

namespace OAI

section Inline_PCPBoundary

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Distances
variable {S H : Type} [Fintype S]

theorem table_distance_triangle (f g h : S → H) :
    testRate (fun x => f x ≠ h x) ≤
      testRate (fun x => f x ≠ g x) + testRate (fun x => g x ≠ h x) := by
  apply testRate_union_bound
  intro x hx
  by_contra hh
  push Not at hh
  exact hx (hh.1.trans hh.2)

theorem table_distance_symm (f g : S → H) :
    testRate (fun x => f x ≠ g x) = testRate (fun x => g x ≠ f x) :=
  testRate_congr (fun _ => ne_comm)
end Distances

section Derivative
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H]

theorem derivative_distance (f : G → H) (g : G →+ H) (x : G) :
    testRate (fun y => derivative f x y ≠ g x) ≤
      2 * testRate (fun y => f y ≠ g y) := by
  have hh : testRate (fun y => derivative f x y ≠ g x) ≤
      testRate (fun y => f (x+y) ≠ g (x+y)) +
      testRate (fun y => f y ≠ g y) := by
    apply testRate_union_bound
    intro y hy
    by_contra hh
    push Not at hh
    apply hy
    simp [derivative, hh.1, hh.2]
  have he := testRate_equiv (Equiv.addLeft x) (fun y => f y ≠ g y)
  change testRate (fun y => f (x+y) ≠ g (x+y)) = _ at he
  rw [he] at hh
  linarith only [hh]
end Derivative

section Code
variable {I : Type} [Fintype I] [DecidableEq I]

@[simp] theorem dot_single (a : BitVector I) (i : I) :
    dot a (Pi.single i 1) = a i := by
  simp [dot, Pi.single_apply, mul_ite]

theorem hadamard_distance (a b : BitVector I) (hab : a ≠ b) :
    testRate (fun x => dot a x ≠ dot b x) = 1/2 := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  let g : BitVector I →+ Bit := dotHom a - dotHom b
  have hg : g (Pi.single i 1) ≠ 0 := by
    change dot a (Pi.single i 1) - dot b (Pi.single i 1) ≠ 0
    simpa only [dot_single, sub_ne_zero] using hi
  have hh := linear_nonzero_rate g (Pi.single i 1) hg
  have he : testRate (fun x => g x ≠ 0) = testRate (fun x => dot a x ≠ dot b x) := by
    apply testRate_congr
    intro x
    exact sub_ne_zero
  rwa [he] at hh

private theorem exists_nearest (f : BitVector I → Bit) :
    ∃ a : BitVector I, ∀ b, testRate (fun x => f x ≠ dot a x) ≤
      testRate (fun x => f x ≠ dot b x) := by
  classical
  obtain ⟨a,_,ha⟩ := univ.exists_min_image
    (fun b : BitVector I => testRate (fun x => f x ≠ dot b x)) univ_nonempty
  exact ⟨a,fun b => ha b (mem_univ b)⟩

noncomputable def nearestLabel (f : BitVector I → Bit) : BitVector I :=
  Classical.choose (exists_nearest f)

theorem nearestLabel_min (f : BitVector I → Bit) (a : BitVector I) :
    testRate (fun x => f x ≠ dot (nearestLabel f) x) ≤
      testRate (fun x => f x ≠ dot a x) := (Classical.choose_spec (exists_nearest f)) a

theorem nearestLabel_robust (f : BitVector I → Bit) (a : BitVector I)
    (ha : a ≠ nearestLabel f) :
    1/4 ≤ testRate (fun x => f x ≠ dot a x) := by
  have hdist := hadamard_distance a (nearestLabel f) ha
  have htri := table_distance_triangle (dot a) f (dot (nearestLabel f))
  rw [table_distance_symm (dot a) f, hdist] at htri
  have hmin := nearestLabel_min f a
  linarith only [htri, hmin]
end Code

section Boundary
variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

def liftQuery (embed : I → V) (x : BitVector I) : BitVector V :=
  ∑ i, x i • Pi.single (embed i) 1

omit [DecidableEq I] in
@[simp] theorem dot_liftQuery (embed : I → V) (a : BitVector V) (x : BitVector I) :
    dot a (liftQuery embed x) = dot (a ∘ embed) x := by
  simp only [liftQuery, dot_sum, dot_smul, dot_single]
  unfold dot
  apply sum_congr rfl
  intro i _
  simp only [Function.comp_apply, mul_comm]

noncomputable def boundaryRate (embed : I → V) (f : BitVector V → Bit)
    (u : BitVector I → Bit) : ℝ :=
  testRate (fun p : BitVector I × BitVector V =>
    derivative f (liftQuery embed p.1) p.2 ≠ u p.1)

theorem boundary_transfer (embed : I → V) (f : BitVector V → Bit)
    (u : BitVector I → Bit) (a : BitVector V) :
    testRate (fun x => u x ≠ dot (a ∘ embed) x) ≤
      boundaryRate embed f u + 2 * testRate (fun y => f y ≠ dot a y) := by
  let P := fun p : BitVector I × BitVector V => u p.1 ≠ dot (a ∘ embed) p.1
  let A := fun p : BitVector I × BitVector V =>
    derivative f (liftQuery embed p.1) p.2 ≠ u p.1
  let B := fun p : BitVector I × BitVector V =>
    derivative f (liftQuery embed p.1) p.2 ≠ dot a (liftQuery embed p.1)
  have hcover : ∀ p, P p → A p ∨ B p := by
    intro p hp
    by_contra hh
    simp only [A, B, not_or, not_not, dot_liftQuery] at hh
    exact hp (hh.1.symm.trans hh.2)
  have hb : testRate B ≤ 2 * testRate (fun y => f y ≠ dot a y) :=
    testRate_fibers_le (S := BitVector I) (T := BitVector V)
      (fun x y => derivative f (liftQuery embed x) y ≠ dot a (liftQuery embed x))
      (2 * testRate (fun y => f y ≠ dot a y))
      (fun x => derivative_distance f (dotHom a) (liftQuery embed x))
  have hp := testRate_union_bound hcover
  have hP : testRate P = testRate (fun x => u x ≠ dot (a ∘ embed) x) :=
    testRate_fst (T := BitVector V) (fun x => u x ≠ dot (a ∘ embed) x)
  rw [hP] at hp
  change testRate (fun x => u x ≠ dot (a ∘ embed) x) ≤
    boundaryRate embed f u + testRate B at hp
  linarith only [hp, hb]
end Boundary
end MetricKMedian.PCP

end Inline_PCPBoundary

end OAI
