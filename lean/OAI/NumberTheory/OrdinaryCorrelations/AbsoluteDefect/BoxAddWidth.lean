import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrefixSet

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
open Finset MeasureTheory
lemma box_add_width {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) :
    box (A+B) x=box A x+box B (x-A) := by
  by_cases hx : 0 < x
  · by_cases hxA : x ≤ A
    · have h1 : x∈Set.Ioc 0 (A+B) := ⟨hx,by linarith⟩
      have h2 : x∈Set.Ioc 0 A := ⟨hx,hxA⟩
      have h3 : x-A∉Set.Ioc 0 B := by intro h; linarith [h.1]
      simp [box,Set.indicator_of_mem h1,Set.indicator_of_mem h2,Set.indicator_of_notMem h3]
    · by_cases hxAB : x ≤ A+B
      · have h1 : x∈Set.Ioc 0 (A+B) := ⟨hx,hxAB⟩
        have h2 : x∉Set.Ioc 0 A := by intro h; exact hxA h.2
        have h3 : x-A∈Set.Ioc 0 B := ⟨by linarith,by linarith⟩
        simp [box,Set.indicator_of_mem h1,Set.indicator_of_notMem h2,Set.indicator_of_mem h3]
      · have h1 : x∉Set.Ioc 0 (A+B) := by intro h; exact hxAB h.2
        have h2 : x∉Set.Ioc 0 A := by intro h; exact hxA h.2
        have h3 : x-A∉Set.Ioc 0 B := by intro h; linarith [h.2]
        simp [box,Set.indicator_of_notMem h1,Set.indicator_of_notMem h2,Set.indicator_of_notMem h3]
  · have h1 : x∉Set.Ioc 0 (A+B) := by intro h; exact hx h.1
    have h2 : x∉Set.Ioc 0 A := by intro h; exact hx h.1
    have h3 : x-A∉Set.Ioc 0 B := by intro h; linarith [h.1]
    simp [box,Set.indicator_of_notMem h1,Set.indicator_of_notMem h2,Set.indicator_of_notMem h3]

lemma sharpWindow_width_add {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) :
    sharpWindow s a u (A+B) x=sharpWindow s a u A x+sharpWindow s a u B (x-A) := by
  unfold sharpWindow
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [box_add_width hA hB,Complex.ofReal_add,mul_add]
  congr 2
  congr 1
  ring_nf

lemma sharpWindow_width_subadditive {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫x : ℝ,‖sharpWindow s a u (A+B) x‖) ≤
      (∫x : ℝ,‖sharpWindow s a u A x‖)+(∫x : ℝ,‖sharpWindow s a u B x‖) := by
  have h1 := (sharpWindow_integrable s a u A).norm
  have h2 := (sharpWindow_integrable s a u B).norm.comp_sub_right A
  calc
    _ ≤ ∫x : ℝ,‖sharpWindow s a u A x‖+‖sharpWindow s a u B (x-A)‖ := by
      apply integral_mono (sharpWindow_integrable s a u (A+B)).norm (h1.add h2)
      intro x
      dsimp only [Pi.add_apply]
      rw [sharpWindow_width_add s a u hA hB]
      exact norm_add_le _ _
    _ = _ := by
      rw [integral_add h1 h2]
      congr 1
      exact integral_sub_right_eq_self (fun x : ℝ=>‖sharpWindow s a u B x‖) A

lemma sharpWindow_width_nat_mul {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {L : ℝ} (hL : 0 ≤ L) (k : ℕ) :
    (∫x : ℝ,‖sharpWindow s a u ((k:ℝ)*L) x‖) ≤
      (k:ℝ)*(∫x : ℝ,‖sharpWindow s a u L x‖) := by
  induction k with
  | zero => simp [sharpWindow,box]
  | succ k ih =>
    have he : ((k+1:ℕ):ℝ)*L=(k:ℝ)*L+L := by push_cast; ring
    rw [he]
    have hh := sharpWindow_width_subadditive s a u (mul_nonneg (Nat.cast_nonneg k) hL) hL
    have hb := _root_.add_le_add ih (le_refl (∫x : ℝ,‖sharpWindow s a u L x‖))
    apply hh.trans
    convert hb using 1
    push_cast
    ring

lemma sharpWindow_l1_mass {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {D : ℝ} (hD : 0 ≤ D) :
    (∫x : ℝ,‖sharpWindow s a u D x‖) ≤ D*(∑n∈s,‖a n‖) := by
  have hi (n : ι) : Integrable (fun x : ℝ=>‖a n‖*box D (x-u n)) :=
    ((box_integrable D).comp_sub_right (u n)).const_mul _
  calc
    _ ≤ ∫x : ℝ,∑n∈s,‖a n‖*box D (x-u n) :=
      integral_mono (sharpWindow_integrable s a u D).norm
        (integrable_finsetSum s (fun n hn=>hi n)) (sharpWindow_norm_le s a u D)
    _ = _ := by
      rw [integral_finsetSum s (fun n hn=>hi n)]
      have he (n : ι) : (∫x : ℝ,‖a n‖*box D (x-u n))=‖a n‖*D := by
        rw [MeasureTheory.integral_const_mul,integral_sub_right_eq_self,box_integral hD]
      simp_rw [he]
      rw [← sum_mul,mul_comm]

lemma sharpWindow_long_from_short {ι : Type*} (s : Finset ι) (a : ι→ℂ) (u : ι→ℝ)
    {L D : ℝ} (hL : 0 < L) (hD : 0 ≤ D) :
    (∫x : ℝ,‖sharpWindow s a u D x‖) ≤
      (D/L)*(∫x : ℝ,‖sharpWindow s a u L x‖)+L*(∑n∈s,‖a n‖) := by
  let k : ℕ := ⌊D/L⌋₊
  have hk : (k:ℝ) ≤ D/L := Nat.floor_le (div_nonneg hD hL.le)
  have hkprod : (k:ℝ)*L ≤ D := (le_div_iff₀ hL).mp hk
  have hk1 : D/L < (k:ℝ)+1 := Nat.lt_floor_add_one (D/L)
  have hr : 0 ≤ D-(k:ℝ)*L := sub_nonneg.mpr hkprod
  have hrL : D-(k:ℝ)*L ≤ L := by have hh := (div_lt_iff₀ hL).mp hk1; nlinarith only [hh]
  have he : D=(k:ℝ)*L+(D-(k:ℝ)*L) := by ring
  have hh := sharpWindow_width_subadditive s a u (mul_nonneg (Nat.cast_nonneg k) hL.le) hr
  rw [← he] at hh
  apply hh.trans
  apply _root_.add_le_add
  · exact (sharpWindow_width_nat_mul s a u hL.le k).trans
      (mul_le_mul_of_nonneg_right hk (integral_nonneg (fun x=>norm_nonneg _)))
  · exact (sharpWindow_l1_mass s a u hr).trans
      (mul_le_mul_of_nonneg_right hrL (sum_nonneg (fun n hn=>norm_nonneg _)))

end OrdinarySharpWindow

end

end OAI
