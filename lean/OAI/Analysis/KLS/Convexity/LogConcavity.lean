import OAI.Analysis.KLS.Model
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

namespace OAI

noncomputable section
open Set
open scoped ENNReal

namespace LeanBlast.KLS

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure IsLogConcaveFunction (f : E → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ f x
  log_concave : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x))

theorem IsLogConcaveDensity.isLogConcaveFunction {n : ℕ} {ρ : Space n → ℝ}
    (hρ : IsLogConcaveDensity ρ) : IsLogConcaveFunction ρ :=
  ⟨hρ.nonnegative, hρ.log_concave⟩

theorem IsLogConcaveFunction.rpow_le {f : E → ℝ} (hf : IsLogConcaveFunction f)
    (x y : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y) := by
  by_cases hx : 0 < f x
  · by_cases hy : 0 < f y
    · have hz : 0 < f (t • x + (1 - t) • y) :=
        hf.log_concave.1 hx hy ht0.le (sub_pos.mpr ht1).le (by ring)
      have hl := hf.log_concave.2 hx hy ht0.le (sub_pos.mpr ht1).le (by ring)
      rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add,
        ← Real.exp_log hz]
      apply Real.exp_le_exp.mpr
      simpa only [smul_eq_mul, mul_comm] using hl
    · have hy0 : f y = 0 := le_antisymm (le_of_not_gt hy) (hf.nonnegative y)
      rw [hy0, Real.zero_rpow (sub_pos.mpr ht1).ne', mul_zero]
      exact hf.nonnegative _
  · have hx0 : f x = 0 := le_antisymm (le_of_not_gt hx) (hf.nonnegative x)
    rw [hx0, Real.zero_rpow ht0.ne', zero_mul]
    exact hf.nonnegative _

theorem IsLogConcaveFunction.ennreal_rpow_le {f : E → ℝ} (hf : IsLogConcaveFunction f)
    (x y : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (f x) ^ t * ENNReal.ofReal (f y) ^ (1 - t) ≤
      ENNReal.ofReal (f (t • x + (1 - t) • y)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (hf.nonnegative x) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (hf.nonnegative y) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf.nonnegative x) t)]
  exact ENNReal.ofReal_le_ofReal (hf.rpow_le x y ht0 ht1)

theorem isLogConcaveFunction_of_rpow_le {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (h : ∀ x y : E, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    IsLogConcaveFunction f := by
  have hw {x y : E} (hx : 0 < f x) (hy : 0 < f y) {a b : ℝ}
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      0 < f (a • x + b • y) ∧
        a * Real.log (f x) + b * Real.log (f y) ≤ Real.log (f (a • x + b • y)) := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [ha0, hb1, hy]
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simp [hb0, ha1, hx]
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hba : 1 - a = b := by linarith
    have hi := h x y a ha' (by linarith)
    rw [hba] at hi
    have hp : 0 < f x ^ a * f y ^ b :=
      mul_pos (Real.rpow_pos_of_pos hx a) (Real.rpow_pos_of_pos hy b)
    have hz : 0 < f (a • x + b • y) := hp.trans_le hi
    refine ⟨hz, (Real.le_log_iff_exp_le hz).mpr ?_⟩
    simpa only [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, Real.exp_add,
      mul_comm] using hi
  exact ⟨hf0, ⟨fun _ hx _ hy _ _ ha hb hab => (hw hx hy ha hb hab).1,
    fun _ hx _ hy _ _ ha hb hab => by
      simpa only [smul_eq_mul] using (hw hx hy ha hb hab).2⟩⟩

theorem isLogConcaveFunction_of_ennreal {f : E → ℝ≥0∞}
    (hfinite : ∀ x, f x ≠ ⊤)
    (h : ∀ x y : E, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    IsLogConcaveFunction (fun x => (f x).toReal) := by
  apply isLogConcaveFunction_of_rpow_le (fun x => ENNReal.toReal_nonneg)
  intro x y t ht0 ht1
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (hfinite _) (h x y t ht0 ht1)

theorem IsLogConcaveFunction.mul_exp {f u : E → ℝ} (hf : IsLogConcaveFunction f)
    (hu : ConcaveOn ℝ univ u) : IsLogConcaveFunction (fun x => f x * Real.exp (u x)) := by
  have hs : {x | 0 < f x * Real.exp (u x)} = {x | 0 < f x} := by
    ext x
    exact mul_pos_iff_of_pos_right (Real.exp_pos (u x))
  refine ⟨fun x => mul_nonneg (hf.nonnegative x) (Real.exp_pos _).le, ?_⟩
  rw [hs]
  apply (hf.log_concave.add (hu.subset (subset_univ _) hf.log_concave.1)).congr
  intro x hx
  simp only [Pi.add_apply, Real.log_mul (ne_of_gt hx) (Real.exp_ne_zero _), Real.log_exp]

theorem IsLogConcaveFunction.exp_mul {f u : E → ℝ} (hf : IsLogConcaveFunction f)
    (hu : ConcaveOn ℝ univ u) : IsLogConcaveFunction (fun x => Real.exp (u x) * f x) := by
  simpa only [mul_comm] using hf.mul_exp hu

theorem IsLogConcaveFunction.const_mul {f : E → ℝ} (hf : IsLogConcaveFunction f)
    {c : ℝ} (hc : 0 < c) : IsLogConcaveFunction (fun x => c * f x) := by
  have h := hf.exp_mul (concaveOn_const (Real.log c) (convex_univ : Convex ℝ (univ : Set E)))
  simpa only [Real.exp_log hc] using h

theorem IsLogConcaveFunction.div_const {f : E → ℝ} (hf : IsLogConcaveFunction f)
    {c : ℝ} (hc : 0 < c) : IsLogConcaveFunction (fun x => f x / c) := by
  simpa only [div_eq_mul_inv, mul_comm] using hf.const_mul (inv_pos.mpr hc)

theorem IsLogConcaveFunction.mul {f g : E → ℝ} (hf : IsLogConcaveFunction f)
    (hg : IsLogConcaveFunction g) : IsLogConcaveFunction (fun x => f x * g x) := by
  apply isLogConcaveFunction_of_rpow_le (fun x => mul_nonneg (hf.nonnegative x) (hg.nonnegative x))
  intro x y t ht0 ht1
  rw [Real.mul_rpow (hf.nonnegative x) (hg.nonnegative x),
    Real.mul_rpow (hf.nonnegative y) (hg.nonnegative y)]
  have h := mul_le_mul (hf.rpow_le x y ht0 ht1) (hg.rpow_le x y ht0 ht1)
    (mul_nonneg (Real.rpow_nonneg (hg.nonnegative x) t)
      (Real.rpow_nonneg (hg.nonnegative y) (1 - t))) (hf.nonnegative _)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem IsLogConcaveFunction.comp_linearMap {F : Type*} [AddCommGroup F] [Module ℝ F]
    {f : F → ℝ} (hf : IsLogConcaveFunction f) (L : E →ₗ[ℝ] F) :
    IsLogConcaveFunction (fun x => f (L x)) := by
  apply isLogConcaveFunction_of_rpow_le (fun x => hf.nonnegative (L x))
  intro x y t ht0 ht1
  simpa only [map_add, map_smul] using hf.rpow_le (L x) (L y) ht0 ht1

end LeanBlast.KLS

end

end OAI
