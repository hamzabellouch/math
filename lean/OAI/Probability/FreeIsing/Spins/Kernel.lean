import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

namespace Problem367

@[simp] theorem isingSpin_neg_ne_pos : IsingSpin.neg ≠ IsingSpin.pos := by decide

@[simp] theorem isingSpin_pos_ne_neg : IsingSpin.pos ≠ IsingSpin.neg := by decide

private theorem spinKernel_univ : (Finset.univ : Finset IsingSpin) = {.neg, .pos} := by decide

theorem sum_isingSpin {α : Type*} [AddCommMonoid α] (f : IsingSpin → α) :
    ∑ a : IsingSpin, f a = f .neg + f .pos := by
  simp [spinKernel_univ]

def spinSign : IsingSpin → ℝ
  | .neg => -1
  | .pos => 1

@[simp] theorem spinSign_neg : spinSign .neg = -1 := rfl
@[simp] theorem spinSign_pos : spinSign .pos = 1 := rfl

@[simp] theorem spinSign_sq (a : IsingSpin) : spinSign a ^ 2 = 1 := by
  cases a <;> norm_num [spinSign]

@[simp] theorem spinSign_mul_self (a : IsingSpin) : spinSign a * spinSign a = 1 := by
  simpa only [pow_two] using spinSign_sq a

theorem spinSign_mul (a b : IsingSpin) :
    spinSign a * spinSign b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [spinSign]

def transitionKernel (theta : ℝ) (a b : IsingSpin) : ℝ :=
  (1 + theta * spinSign a * spinSign b) / 2

theorem transitionKernel_eq (theta : ℝ) (a b : IsingSpin) :
    transitionKernel theta a b = (1 + (if a = b then theta else -theta)) / 2 := by
  cases a <;> cases b <;> simp [transitionKernel, spinSign]

theorem transitionKernel_symm (theta : ℝ) (a b : IsingSpin) :
    transitionKernel theta a b = transitionKernel theta b a := by
  unfold transitionKernel
  ring

@[simp] theorem transitionKernel_zero (a b : IsingSpin) :
    transitionKernel 0 a b = (1 / 2 : ℝ) := by
  simp [transitionKernel]

@[simp] theorem transitionKernel_one (a b : IsingSpin) :
    transitionKernel 1 a b = if a = b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [transitionKernel, spinSign]

@[simp] theorem sum_spinSign : ∑ a : IsingSpin, spinSign a = 0 := by
  simp [sum_isingSpin, spinSign]

@[simp] theorem transitionKernel_sum (theta : ℝ) (a : IsingSpin) :
    ∑ b : IsingSpin, transitionKernel theta a b = 1 := by
  rw [sum_isingSpin]
  simp only [transitionKernel, spinSign_neg, spinSign_pos]
  ring

@[simp] theorem transitionKernel_spinSum (theta : ℝ) (a : IsingSpin) :
    ∑ b : IsingSpin, transitionKernel theta a b * spinSign b = theta * spinSign a := by
  rw [sum_isingSpin]
  simp only [transitionKernel, spinSign_neg, spinSign_pos]
  ring

theorem transitionKernel_comp (s t : ℝ) (a c : IsingSpin) :
    ∑ b : IsingSpin, transitionKernel s a b * transitionKernel t b c =
      transitionKernel (s * t) a c := by
  rw [sum_isingSpin]
  simp only [transitionKernel, spinSign_neg, spinSign_pos]
  ring

theorem transitionKernel_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (a b : IsingSpin) : 0 ≤ transitionKernel theta a b := by
  rw [transitionKernel_eq]
  split_ifs <;> linarith

theorem transitionKernel_le_one {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (a b : IsingSpin) : transitionKernel theta a b ≤ 1 := by
  rw [transitionKernel_eq]
  split_ifs <;> linarith

def transitionKernelIter (theta : ℝ) : ℕ → IsingSpin → IsingSpin → ℝ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, c => ∑ b : IsingSpin,
      transitionKernelIter theta n a b * transitionKernel theta b c

theorem transitionKernelIter_eq (theta : ℝ) (n : ℕ) (a b : IsingSpin) :
    transitionKernelIter theta n a b = transitionKernel (theta ^ n) a b := by
  induction n generalizing a b with
  | zero => simp [transitionKernelIter]
  | succ n ih =>
    simp only [transitionKernelIter, ih, transitionKernel_comp, pow_succ]

@[simp] theorem transitionKernelIter_sum (theta : ℝ) (n : ℕ) (a : IsingSpin) :
    ∑ b : IsingSpin, transitionKernelIter theta n a b = 1 := by
  simp only [transitionKernelIter_eq, transitionKernel_sum]

theorem transitionKernelIter_spinSum (theta : ℝ) (n : ℕ) (a : IsingSpin) :
    ∑ b : IsingSpin, transitionKernelIter theta n a b * spinSign b =
      theta ^ n * spinSign a := by
  simp only [transitionKernelIter_eq, transitionKernel_spinSum]

theorem transitionKernel_stationary (theta : ℝ) (b : IsingSpin) :
    ∑ a : IsingSpin, (1 / 2 : ℝ) * transitionKernel theta a b = 1 / 2 := by
  rw [sum_isingSpin]
  simp only [transitionKernel, spinSign_neg, spinSign_pos]
  ring

theorem transitionKernelIter_correlation (theta : ℝ) (n : ℕ) :
    ∑ a : IsingSpin, ∑ b : IsingSpin,
      (1 / 2 : ℝ) * transitionKernelIter theta n a b * spinSign a * spinSign b =
        theta ^ n := by
  simp only [transitionKernelIter_eq, sum_isingSpin, transitionKernel,
    spinSign_neg, spinSign_pos]
  ring

theorem freeCylinderWeight_eq_transitionKernel {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ e ∈ inducedEdges D, transitionKernel theta (eta e.1) (eta e.2)) := by
  simp only [freeCylinderWeight, transitionKernel_eq]

end Problem367

end

end OAI
