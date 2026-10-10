import OAI.Probability.SignedSweeps.KernelBounds

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}

lemma marginal_kernel_eq_zero (e : J ↪ I)
    (K : InjectiveTuple I n → InjectiveTuple J n → ℝ)
    (f : TupleSpace I n) (hf : tupleMarginal e f = 0) :
    kernelOperator (fun x y : InjectiveTuple I n => K x (e.trans y)) f = 0 := by
  apply PiLp.ext
  intro x
  change (∑ y, (K x (e.trans y) : ℂ) * f y) = 0
  calc
    _ = ∑ z : InjectiveTuple J n, (K x z : ℂ) * tupleMarginal e f z := by
      change _ = ∑ z : InjectiveTuple J n, (K x z : ℂ) *
        ∑ y, if e.trans y = z then f y else 0
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = 0 := by simp only [hf, PiLp.zero_apply, mul_zero, Finset.sum_const_zero]

lemma specht_marginal_kernel_eq_zero {n : ℕ} (lam : Partition n)
    {J : Type*} [Fintype J] (e : J ↪ OffFirstRow lam)
    (he : Fintype.card J < n - lam.1.rowLen 0)
    (K : InjectiveTuple (OffFirstRow lam) n → InjectiveTuple J n → ℝ)
    (f : Specht lam) :
    kernelOperator (fun x y => K x (e.trans y)) (tupleRealization lam f) = 0 :=
  marginal_kernel_eq_zero e K _ (tupleRealization_marginal_eq_zero lam e he f)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma alternating_subsets_cancel (F : Finset I → ℝ) (i : I)
    (hF : ∀ A : Finset I, i ∉ A → F (insert i A) = F A) :
    (∑ A : Finset I, (-1 : ℝ) ^ A.card * F A) = 0 := by
  have hu : (Finset.univ : Finset (Finset I)) = (insert i ((Finset.univ : Finset I).erase i)).powerset := by
    simp only [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ]
  rw [hu, Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro A hA
  have hi : i ∉ A := by
    exact fun h => (Finset.notMem_erase i Finset.univ) ((Finset.mem_powerset.mp hA) h)
  rw [Finset.card_insert_of_notMem hi, pow_succ, hF A hi]
  ring

omit [DecidableEq I] in
lemma alternating_full_coefficient :
    (-1 : ℝ) ^ Fintype.card I * (-1) ^ (Finset.univ : Finset I).card = 1 := by
  rw [Finset.card_univ, ← mul_pow]
  norm_num

def differenceKernel {X Y : Type*} (K : Finset I → X → Y → ℝ) (x : X) (y : Y) : ℝ :=
  (-1 : ℝ) ^ Fintype.card I * ∑ A : Finset I, (-1 : ℝ) ^ A.card * K A x y

lemma differenceKernel_vanishes_of_isolate {X Y : Type*}
    (K : Finset I → X → Y → ℝ) (x : X) (y : Y) (i : I)
    (hi : ∀ A : Finset I, i ∉ A → K (insert i A) x y = K A x y) :
    differenceKernel K x y = 0 := by
  rw [differenceKernel, alternating_subsets_cancel (fun A => K A x y) i hi, mul_zero]

omit [DecidableEq I] in
lemma differenceKernel_action {X : Type*} [Fintype X]
    (K : Finset I → X → X → ℝ) (f : EuclideanSpace ℂ X)
    (hproper : ∀ A : Finset I, A ≠ Finset.univ → kernelOperator (K A) f = 0) :
    kernelOperator (differenceKernel K) f = kernelOperator (K Finset.univ) f := by
  apply PiLp.ext
  intro x
  change (∑ y, (differenceKernel K x y : ℂ) * f y) = _
  simp only [differenceKernel, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (A : Finset I) :
      (∑ y : X, ((-1 : ℂ) ^ Fintype.card I * ((-1) ^ A.card * (K A x y : ℂ))) * f y) =
      (-1 : ℂ) ^ Fintype.card I * (-1) ^ A.card * kernelOperator (K A) f x := by
    rw [kernelOperator_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [he]
  rw [Finset.sum_eq_single Finset.univ]
  · have hs : (-1 : ℂ) ^ Fintype.card I * (-1) ^ (Finset.univ : Finset I).card = 1 := by
      rw [Finset.card_univ, ← mul_pow]
      norm_num
    rw [hs, one_mul]
  · intro A _ hA
    rw [hproper A hA]
    simp
  · simp

end SignedSweeps
end

end OAI
