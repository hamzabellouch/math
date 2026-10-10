import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge
import OAI.Analysis.MutuallyUnbiased.Moments.AverageAlgebra

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

def reindex (f : ι → κ) (v : Sparse ι) : Sparse κ :=
  v.map fun p => (f p.1, p.2)

@[simp] theorem eval_reindex (f : ι → κ) (v : Sparse ι) (x : κ → ℝ) :
    eval (reindex f v) x = eval v (x ∘ f) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    change (p.2 : ℝ) * x (f p.1) + eval (reindex f v) x =
      (p.2 : ℝ) * x (f p.1) + eval v (x ∘ f)
    rw [ih]

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

namespace Integer.Sparse

variable {ι κ Ω : Type*}

def reindex (f : ι → κ) (v : Integer.Sparse ι) : Integer.Sparse κ :=
  v.map fun p => (f p.1, p.2)

@[simp] theorem eval_reindex (f : ι → κ) (v : Integer.Sparse ι) (x : κ → ℝ) :
    eval (reindex f v) x = eval v (x ∘ f) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    change (p.2 : ℝ) * x (f p.1) + eval (reindex f v) x =
      (p.2 : ℝ) * x (f p.1) + eval v (x ∘ f)
    rw [ih]

def toRational (v : Integer.Sparse ι) : Certificate.Sparse ι :=
  v.map fun p => (p.1, (p.2 : ℚ))

@[simp] theorem eval_toRational (v : Integer.Sparse ι) (x : ι → ℝ) :
    Certificate.Sparse.eval (toRational v) x = eval v x := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    change ((p.2 : ℚ) : ℝ) * x p.1 + Certificate.Sparse.eval (toRational v) x =
      (p.2 : ℝ) * x p.1 + eval v x
    rw [ih]
    simp

theorem eval_average [Fintype Ω] (v : Integer.Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Integer.Sparse
end MUB6.Certificate

end OAI
