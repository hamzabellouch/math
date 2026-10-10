import OAI.Algebra.AuslanderReiten.Cocycles.CocycleDifferential
import OAI.Algebra.AuslanderReiten.Cocycles.SparseParity

namespace OAI

namespace ArExplicit.CocycleData

def certificate (a : TIndex) : Bool :=
  SparseParity.paired (SparseParity.sort (fun x y => decide (x.number ≤ y.number)) (differentialBlock a))

private theorem valid_false_e : certificate (false, .e) = true := by decide +kernel

private theorem valid_false_x : certificate (false, .x) = true := by decide +kernel

private theorem valid_false_y : certificate (false, .y) = true := by decide +kernel

private theorem valid_false_z : certificate (false, .z) = true := by decide +kernel

private theorem valid_false_u : certificate (false, .u) = true := by decide +kernel

private theorem valid_false_v : certificate (false, .v) = true := by decide +kernel

private theorem valid_false_t : certificate (false, .t) = true := by decide +kernel

private theorem valid_false_j : certificate (false, .j) = true := by decide +kernel

private theorem valid_false_f : certificate (false, .f) = true := by decide +kernel

private theorem valid_false_n : certificate (false, .n) = true := by decide +kernel

private theorem valid_true_e : certificate (true, .e) = true := by decide +kernel

private theorem valid_true_x : certificate (true, .x) = true := by decide +kernel

private theorem valid_true_y : certificate (true, .y) = true := by decide +kernel

private theorem valid_true_z : certificate (true, .z) = true := by decide +kernel

private theorem valid_true_u : certificate (true, .u) = true := by decide +kernel

private theorem valid_true_v : certificate (true, .v) = true := by decide +kernel

private theorem valid_true_t : certificate (true, .t) = true := by decide +kernel

private theorem valid_true_j : certificate (true, .j) = true := by decide +kernel

private theorem valid_true_f : certificate (true, .f) = true := by decide +kernel

private theorem valid_true_n : certificate (true, .n) = true := by decide +kernel

theorem certificate_valid (a : TIndex) : certificate a = true := by
  obtain ⟨b, i⟩ := a
  cases b <;> cases i
  · exact valid_false_e
  · exact valid_false_x
  · exact valid_false_y
  · exact valid_false_z
  · exact valid_false_u
  · exact valid_false_v
  · exact valid_false_t
  · exact valid_false_j
  · exact valid_false_f
  · exact valid_false_n
  · exact valid_true_e
  · exact valid_true_x
  · exact valid_true_y
  · exact valid_true_z
  · exact valid_true_u
  · exact valid_true_v
  · exact valid_true_t
  · exact valid_true_j
  · exact valid_true_f
  · exact valid_true_n

theorem differentialBlock_sum_zero {M : Type*} [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : QuadMonomial → M) (a : TIndex) :
    ((differentialBlock a).map f).sum = 0 :=
  SparseParity.sum_eq_zero_of_sorted_paired hchar f _ _ (certificate_valid a)

private theorem sum_partition {α ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (l : List α) (key : α → ι) (f : α → M) :
    (l.map f).sum = ∑ i, ((l.filter fun a => decide (key a = i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hstep (i : ι) :
        (((a :: l).filter fun x => decide (key x = i)).map f).sum =
          (if key a = i then f a else 0) + ((l.filter fun x => decide (key x = i)).map f).sum := by
      by_cases h : key a = i <;> simp [h]
    simp_rw [hstep]
    simp [Finset.sum_add_distrib, ← ih]

theorem differentialTerms_sum_zero {M : Type*} [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : QuadMonomial → M) :
    (differentialTerms.map f).sum = 0 := by
  rw [sum_partition differentialTerms QuadMonomial.first f]
  apply Finset.sum_eq_zero
  intro a _
  rw [← differentialBlock_eq]
  exact differentialBlock_sum_zero hchar f a

end ArExplicit.CocycleData

end OAI
