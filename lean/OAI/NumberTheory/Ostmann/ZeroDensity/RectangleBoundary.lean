import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleLogIntegrals

namespace OAI

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval BigOperators

structure RectangleIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b
  top : IntervalIntegrable (fun x : ℝ => f (x + d * I)) volume a b
  right : IntervalIntegrable (fun y : ℝ => f (b + y * I)) volume c d
  left : IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d

theorem RectangleIntegrable.add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    RectangleIntegrable (fun z => f z + g z) a b c d :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top, hf.right.add hg.right, hf.left.add hg.left⟩

theorem rectangleBoundaryIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    rectangleBoundaryIntegral (fun z => f z + g z) a b c d =
      rectangleBoundaryIntegral f a b c d + rectangleBoundaryIntegral g a b c d := by
  simp only [rectangleBoundaryIntegral, intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top, intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  ring

theorem RectangleIntegrable.const_mul {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (v : ℂ) :
    RectangleIntegrable (fun z => v * f z) a b c d :=
  ⟨hf.bottom.const_mul v, hf.top.const_mul v, hf.right.const_mul v, hf.left.const_mul v⟩

theorem rectangleBoundaryIntegral_const_mul (f : ℂ → ℂ) (v : ℂ) (a b c d : ℝ) :
    rectangleBoundaryIntegral (fun z => v * f z) a b c d = v * rectangleBoundaryIntegral f a b c d := by
  simp only [rectangleBoundaryIntegral, intervalIntegral.integral_const_mul]
  ring

theorem RectangleIntegrable.sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {a b c d : ℝ}
    (h : ∀ i ∈ S, RectangleIntegrable (f i) a b c d) :
    RectangleIntegrable (fun z => ∑ i ∈ S, f i z) a b c d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨by simp, by simp, by simp, by simp⟩
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem rectangleBoundaryIntegral_sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    {a b c d : ℝ} (h : ∀ i ∈ S, RectangleIntegrable (f i) a b c d) :
    rectangleBoundaryIntegral (fun z => ∑ i ∈ S, f i z) a b c d =
      ∑ i ∈ S, rectangleBoundaryIntegral (f i) a b c d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectangleBoundaryIntegral]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [rectangleBoundaryIntegral_add (h i (Finset.mem_insert_self _ _))
      (RectangleIntegrable.sum S (fun j hj => h j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

theorem rectangleBoundaryIntegral_translate (f : ℂ → ℂ) (z : ℂ) (a b c d : ℝ) :
    rectangleBoundaryIntegral (fun s => f (s - z)) a b c d =
      rectangleBoundaryIntegral f (a - z.re) (b - z.re) (c - z.im) (d - z.im) := by
  have hh (h : ℝ) (x : ℝ) : (x : ℂ) + h * I - z =
      ((x - z.re : ℝ) : ℂ) + (h - z.im) * I := by
    apply Complex.ext <;> simp
  have hv (h : ℝ) (y : ℝ) : (h : ℂ) + y * I - z =
      ((h - z.re : ℝ) : ℂ) + (y - z.im) * I := by
    apply Complex.ext <;> simp
  have hi (h : ℝ) : (∫ x in a..b, f ((x : ℂ) + h * I - z)) =
      ∫ x in a - z.re..b - z.re, f ((x : ℂ) + (h - z.im) * I) := by
    rw [← intervalIntegral.integral_comp_sub_right (fun x : ℝ => f ((x : ℂ) + (h - z.im) * I)) z.re]
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (hh h x)
  have hj (h : ℝ) : (∫ y in c..d, f ((h : ℂ) + y * I - z)) =
      ∫ y in c - z.im..d - z.im, f (((h - z.re : ℝ) : ℂ) + y * I) := by
    rw [← intervalIntegral.integral_comp_sub_right (fun y : ℝ => f (((h - z.re : ℝ) : ℂ) + y * I)) z.im]
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [Complex.ofReal_sub] using congrArg f (hv h y)
  unfold rectangleBoundaryIntegral
  rw [hi, hi, hj, hj]
  simp only [Complex.ofReal_sub]

theorem rectangleBoundaryIntegral_sub_inv (z : ℂ) (a b c d : ℝ)
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    rectangleBoundaryIntegral (fun s => (s - z)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  rw [rectangleBoundaryIntegral_translate]
  exact rectangleBoundaryIntegral_reciprocal _ _ _ _ (sub_neg.mpr ha) (sub_pos.mpr hb)
    (sub_neg.mpr hc) (sub_pos.mpr hd)

end Ostmann

end OAI
