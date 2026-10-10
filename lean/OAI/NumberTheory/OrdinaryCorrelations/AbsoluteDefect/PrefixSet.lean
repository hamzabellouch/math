import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxNonneg

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinarySharpWindow
open MeasureTheory Finset

noncomputable def prefixSet {ι : Type*} (s : Finset ι) (u : ι→ℝ) (v : ℝ) : Finset ι :=
  s.filter (fun n=>u n ≤ v)
noncomputable def borderSet {ι : Type*} (s : Finset ι) (u : ι→ℝ) (v H : ℝ) : Finset ι :=
  s.filter (fun n=>v-H < u n ∧ u n ≤ v)

lemma prefixWindow_eq_left {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {v H x : ℝ} (hx : x ≤ v) :
    sharpWindow (prefixSet s u v) a u H x=sharpWindow s a u H x := by
  classical
  apply sum_subset (filter_subset _ _)
  intro n hn hnp
  have hnv : ¬u n ≤ v := by simpa only [prefixSet,mem_filter,hn,true_and] using hnp
  have hb : x-u n∉Set.Ioc 0 H := by intro hh; linarith [hh.1,lt_of_not_ge hnv]
  simp [box,Set.indicator_of_notMem hb]

lemma prefixWindow_eq_border {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {v H x : ℝ} (hx : v < x) :
    sharpWindow (prefixSet s u v) a u H x=sharpWindow (borderSet s u v H) a u H x := by
  classical
  symm
  apply sum_subset
  · intro n hn
    obtain ⟨hns,hnv⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hns,hnv.2⟩
  · intro n hn hnb
    obtain ⟨hns,hnv⟩ := mem_filter.mp hn
    have hu : u n ≤ v-H := by
      by_contra hh
      exact hnb (mem_filter.mpr ⟨hns,lt_of_not_ge hh,hnv⟩)
    have hb : x-u n∉Set.Ioc 0 H := by intro hh; linarith [hh.2]
    simp [box,Set.indicator_of_notMem hb]

lemma sharpWindow_norm_le {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ) (H x : ℝ) :
    ‖sharpWindow s a u H x‖ ≤ ∑n∈s,‖a n‖*box H (x-u n) := by
  apply (norm_sum_le _ _).trans_eq
  apply sum_congr rfl
  intro n hn
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (box_nonneg _ _)]

lemma prefixWindow_bound {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ) (v H x : ℝ) :
    ‖sharpWindow (prefixSet s u v) a u H x‖ ≤
      ‖sharpWindow s a u H x‖+∑n∈borderSet s u v H,‖a n‖*box H (x-u n) := by
  rcases le_or_gt x v with hx|hx
  · rw [prefixWindow_eq_left s a u hx]
    exact le_add_of_nonneg_right (sum_nonneg (fun n hn=>mul_nonneg (norm_nonneg _) (box_nonneg _ _)))
  · rw [prefixWindow_eq_border s a u hx]
    exact (sharpWindow_norm_le _ _ _ _ _).trans (le_add_of_nonneg_left (norm_nonneg _))

theorem prefixWindow_l1_bound {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    (v : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (∫x : ℝ,‖sharpWindow (prefixSet s u v) a u H x‖) ≤
      (∫x : ℝ,‖sharpWindow s a u H x‖)+H*(∑n∈borderSet s u v H,‖a n‖) := by
  have ht (n : ι) : Integrable (fun x : ℝ=>‖a n‖*box H (x-u n)) :=
    ((box_integrable H).comp_sub_right (u n)).const_mul _
  have hs := integrable_finsetSum (borderSet s u v H) (fun n hn=>ht n)
  calc
    _ ≤ ∫x : ℝ,‖sharpWindow s a u H x‖+
        ∑n∈borderSet s u v H,‖a n‖*box H (x-u n) :=
      integral_mono (sharpWindow_integrable _ _ _ _).norm
        ((sharpWindow_integrable s a u H).norm.add hs) (prefixWindow_bound s a u v H)
    _ = _ := by
      rw [integral_add (sharpWindow_integrable s a u H).norm hs,
        integral_finsetSum _ (fun n hn=>ht n)]
      have he (n : ι) : (∫x : ℝ,‖a n‖*box H (x-u n))=‖a n‖*H := by
        rw [MeasureTheory.integral_const_mul,integral_sub_right_eq_self,box_integral hH]
      simp_rw [he]
      rw [←sum_mul,mul_comm H]

end OrdinarySharpWindow

end

end OAI
