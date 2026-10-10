import OAI.Analysis.MetricEntropy.Model

namespace OAI

universe uι uX uY

/-!
# Literal finite-dimensional convex bodies and covering numbers

The coordinate space carries its ordinary finite product topology and sup norm.
Polar membership uses the actual real coordinate pairing. Covering centers are
unrestricted ambient vectors. `coveringNumber` is the least finite cover size;
the natural-number empty-infimum convention is zero when no finite cover exists.
The geometric applications prove `Coverable` before using attainment, positivity,
or a lower bound, so that convention never substitutes for a genuine minimum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

def l1Norm {ι : Type uι} [Fintype ι] (x : RealSpace ι) : ℝ :=
  ∑ i, |x i|

def l1Ball (ι : Type uι) [Fintype ι] : Set (RealSpace ι) :=
  {x | l1Norm x ≤ 1}

def row {X : Type uX} {Y : Type uY} (g : Y → X → ℝ) (x : X) : RealSpace Y :=
  fun y => g y x

def columnCombination {X : Type uX} {Y : Type uY} [Fintype Y]
    (g : Y → X → ℝ) (lam : RealSpace Y) : RealSpace X :=
  fun x => ∑ y, lam y * g y x

def UniformClose {X : Type uX} (ε : ℝ) (f h : RealSpace X) : Prop :=
  ∀ x, |f x - h x| ≤ ε

/-- The approximation list may contain functions outside the column hull. -/
def UniformApproximation {X : Type uX} {Y : Type uY} [Fintype Y]
    (g : Y → X → ℝ) (ε : ℝ) (A : Finset (RealSpace X)) : Prop :=
  ∀ lam ∈ l1Ball Y, ∃ a ∈ A, UniformClose ε (columnCombination g lam) a

def absRowHull {X : Type uX} {Y : Type uY} (g : Y → X → ℝ) : Set (RealSpace Y) :=
  convexHull ℝ (Set.range (row g) ∪ Set.range (fun x => -row g x))

def matrixBody {X : Type uX} {Y : Type uY} (g : Y → X → ℝ) (t : ℝ) : Set (RealSpace Y) :=
  (3 : ℝ) • absRowHull g + t • cube Y

section Elementary

variable {ι : Type uι} {X : Type uX} {Y : Type uY} [Fintype ι]

@[simp] theorem pairing_zero_left (y : RealSpace ι) : pairing 0 y = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (x : RealSpace ι) : pairing x 0 = 0 := by
  simp [pairing]

theorem pairing_comm (x y : RealSpace ι) : pairing x y = pairing y x := by
  simp only [pairing, mul_comm]

theorem pairing_add_left (x z y : RealSpace ι) :
    pairing (x + z) y = pairing x y + pairing z y := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (x y z : RealSpace ι) :
    pairing x (y + z) = pairing x y + pairing x z := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_sub_left (x z y : RealSpace ι) :
    pairing (x - z) y = pairing x y - pairing z y := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

theorem pairing_sub_right (x y z : RealSpace ι) :
    pairing x (y - z) = pairing x y - pairing x z := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

theorem pairing_smul_left (a : ℝ) (x y : RealSpace ι) :
    pairing (a • x) y = a * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_assoc]

theorem pairing_smul_right (a : ℝ) (x y : RealSpace ι) :
    pairing x (a • y) = a * pairing x y := by
  rw [pairing_comm, pairing_smul_left, pairing_comm y x]

@[simp] theorem pairing_neg_left (x y : RealSpace ι) :
    pairing (-x) y = -pairing x y := by
  simp [pairing, Finset.sum_neg_distrib]

@[simp] theorem pairing_neg_right (x y : RealSpace ι) :
    pairing x (-y) = -pairing x y := by
  simp [pairing, Finset.sum_neg_distrib]

theorem l1Norm_nonneg (x : RealSpace ι) : 0 ≤ l1Norm x :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (x i))

@[simp] theorem l1Norm_zero : l1Norm (0 : RealSpace ι) = 0 := by
  simp [l1Norm]

@[simp] theorem l1Norm_neg (x : RealSpace ι) : l1Norm (-x) = l1Norm x := by
  simp [l1Norm]

theorem l1Norm_sub_le (x y : RealSpace ι) :
    l1Norm (x - y) ≤ l1Norm x + l1Norm y := by
  calc
    l1Norm (x - y) ≤ ∑ i, (|x i| + |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Pi.sub_apply, sub_eq_add_neg, abs_neg] using abs_add_le (x i) (-y i)
    _ = l1Norm x + l1Norm y := by rw [Finset.sum_add_distrib]; rfl

omit [Fintype ι] in
@[simp] theorem zero_mem_cube : (0 : RealSpace ι) ∈ cube ι := by
  simp [cube]

@[simp] theorem zero_mem_l1Ball : (0 : RealSpace ι) ∈ l1Ball ι := by
  simp [l1Ball]

theorem UniformClose.symm {ε : ℝ} {f h : RealSpace X}
    (hfh : UniformClose ε f h) : UniformClose ε h f := by
  intro x
  simpa only [abs_sub_comm] using hfh x

theorem columnCombination_sub [Fintype Y] (g : Y → X → ℝ)
    (lam μ : RealSpace Y) :
    columnCombination g (lam - μ) = columnCombination g lam - columnCombination g μ := by
  funext x
  simp [columnCombination, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem columnCombination_zero [Fintype Y] (g : Y → X → ℝ) :
    columnCombination g 0 = 0 := by
  funext x
  simp [columnCombination]

theorem pairing_row_eq_columnCombination [Fintype Y]
    (g : Y → X → ℝ) (lam : RealSpace Y) (x : X) :
    pairing (row g x) lam = columnCombination g lam x := by
  simp only [pairing, row, columnCombination, mul_comm]

end Elementary

end MetricEntropyDuality

end

end OAI
