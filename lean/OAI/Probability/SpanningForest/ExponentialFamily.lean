import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.ExponentialFamily

variable {α : Type*} [Fintype α]

def partition (w g : α → ℝ) (t : ℝ) : ℝ :=
  ∑ a, w a * Real.exp (t * g a)

def numerator (w g f : α → ℝ) (t : ℝ) : ℝ :=
  ∑ a, w a * Real.exp (t * g a) * f a

def mean (w g f : α → ℝ) (t : ℝ) : ℝ :=
  numerator w g f t / partition w g t

lemma hasDerivAt_partition (w g : α → ℝ) (t : ℝ) :
    HasDerivAt (partition w g) (numerator w g g t) t := by
  unfold partition numerator
  apply HasDerivAt.fun_sum
  intro a _
  simpa only [id_eq, one_mul, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).mul_const (g a)).exp.const_mul (w a))

lemma hasDerivAt_numerator (w g f : α → ℝ) (t : ℝ) :
    HasDerivAt (numerator w g f)
      (numerator w g (fun a => f a * g a) t) t := by
  unfold numerator
  apply HasDerivAt.fun_sum
  intro a _
  simpa only [id_eq, one_mul, mul_assoc, mul_comm, mul_left_comm] using
    ((((hasDerivAt_id t).mul_const (g a)).exp.const_mul (w a)).mul_const (f a))

theorem hasDerivAt_mean (w g f : α → ℝ) (t : ℝ)
    (hz : partition w g t ≠ 0) :
    HasDerivAt (mean w g f)
      (mean w g (fun a => f a * g a) t - mean w g f t * mean w g g t) t := by
  have h := (hasDerivAt_numerator w g f t).div (hasDerivAt_partition w g t) hz
  apply h.congr_deriv
  unfold mean
  field_simp

lemma partition_pos (w g : α → ℝ) (t : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hpos : ∃ a, 0 < w a) :
    0 < partition w g t := by
  classical
  obtain ⟨a, ha⟩ := hpos
  unfold partition
  exact Finset.sum_pos' (fun b _ => mul_nonneg (hw b) (Real.exp_pos _).le)
    ⟨a, Finset.mem_univ a, mul_pos ha (Real.exp_pos _)⟩

theorem hasDerivAt_mean_of_nonneg (w g f : α → ℝ) (t : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hpos : ∃ a, 0 < w a) :
    HasDerivAt (mean w g f)
      (mean w g (fun a => f a * g a) t - mean w g f t * mean w g g t) t :=
  hasDerivAt_mean w g f t (ne_of_gt (partition_pos w g t hw hpos))

def mass (w g : α → ℝ) (t : ℝ) (a : α) : ℝ :=
  w a * Real.exp (t * g a) / partition w g t

lemma sum_mass (w g : α → ℝ) (t : ℝ) (hz : partition w g t ≠ 0) :
    ∑ a, mass w g t a = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self hz

lemma mass_nonneg (w g : α → ℝ) (t : ℝ) (hw : ∀ a, 0 ≤ w a) (a : α) :
    0 ≤ mass w g t a := by
  unfold mass partition
  exact div_nonneg (mul_nonneg (hw a) (Real.exp_pos _).le)
    (Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (Real.exp_pos _).le))

lemma mean_eq_sum_mass (w g f : α → ℝ) (t : ℝ) :
    mean w g f t = ∑ a, mass w g t a * f a := by
  simp only [mean, numerator, mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma mean_nonneg (w g f : α → ℝ) (t : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean w g f t := by
  rw [mean_eq_sum_mass]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (mass_nonneg w g t hw a) (hf a))

lemma mean_le_const (w g f : α → ℝ) (t c : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hz : partition w g t ≠ 0) (hf : ∀ a, f a ≤ c) :
    mean w g f t ≤ c := by
  rw [mean_eq_sum_mass]
  calc
    ∑ a, mass w g t a * f a ≤ ∑ a, mass w g t a * c :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a)
        (mass_nonneg w g t hw a))
    _ = c := by rw [← Finset.sum_mul, sum_mass w g t hz, one_mul]

lemma mean_mem_Icc (w g f : α → ℝ) (t : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hz : partition w g t ≠ 0)
    (hf : ∀ a, f a ∈ Set.Icc (0 : ℝ) 1) :
    mean w g f t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mean_nonneg w g f t hw (fun a => (hf a).1),
    mean_le_const w g f t 1 hw hz (fun a => (hf a).2)⟩

end Problem336.ExponentialFamily

end

end OAI
