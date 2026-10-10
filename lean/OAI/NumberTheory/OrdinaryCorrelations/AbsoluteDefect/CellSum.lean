import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
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

namespace OrdinaryDiscreteWindows
open OrdinaryCorrelations OrdinarySharpWindow Finset MeasureTheory
noncomputable def cellSum (a : ℕ→ℂ) (N D m : ℕ) : ℂ :=
  ∑n∈(Finset.Ioc 0 N).filter (fun n=>n ≤ m ∧ m < n+D),a n
lemma box_on_unit {D n m : ℕ} {x : ℝ} (hx : x∈Set.Ioc (m:ℝ) ((m:ℝ)+1)) :
    OrdinarySharpWindow.box (D:ℝ) (x-n) = if n ≤ m ∧ m < n+D then 1 else 0 := by
  have he : x-(n:ℝ)∈Set.Ioc 0 (D:ℝ) ↔ n ≤ m ∧ m < n+D := by
    constructor
    · rintro ⟨h1,h2⟩
      constructor
      · by_contra hn
        have hnreal : (m:ℝ)+1≤n := by exact_mod_cast (by omega : m+1≤n)
        linarith only [hx.2,h1,hnreal]
      · by_contra hn
        have hnreal : (n:ℝ)+D≤ m := by exact_mod_cast (by omega : n+D≤ m)
        linarith only [hx.1,h2,hnreal]
    · rintro ⟨h1,h2⟩
      have h1r : (n:ℝ)≤ m := by exact_mod_cast h1
      have h2r : (m:ℝ)+1≤(n:ℝ)+D := by exact_mod_cast h2
      exact ⟨by linarith only [h1r,hx.1],by linarith only [h2r,hx.2]⟩
  simp only [OrdinarySharpWindow.box,Set.indicator_apply,he]
lemma sharpWindow_cell (a : ℕ→ℂ) (N D m : ℕ) {x : ℝ}
    (hx : x∈Set.Ioc (m:ℝ) ((m:ℝ)+1)) :
    sharpWindow (Ioc 0 N) a (fun n=>(n:ℝ)) (D:ℝ) x=cellSum a N D m := by
  unfold sharpWindow cellSum
  simp_rw [box_on_unit hx]
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp
lemma sharpWindow_prefix_support (a : ℕ→ℂ) (N D : ℕ) :
    Function.support (fun x:ℝ=>‖sharpWindow (Ioc 0 N) a (fun n=>(n:ℝ)) (D:ℝ) x‖)
      ⊆ Set.Ioc 0 ((N+D:ℕ):ℝ) := by
  intro x hx
  by_contra hx'
  apply hx
  rw [norm_eq_zero]
  unfold sharpWindow
  apply sum_eq_zero
  intro n hn
  have hm : x-(n:ℝ)∉Set.Ioc 0 (D:ℝ) := by
    intro h
    apply hx'
    have hn0 : (0:ℝ)<n := by exact_mod_cast (mem_Ioc.mp hn).1
    have hnN : (n:ℝ)≤N := by exact_mod_cast (mem_Ioc.mp hn).2
    constructor
    · linarith only [hn0,h.1]
    · push_cast
      linarith only [hnN,h.2]
  simp [OrdinarySharpWindow.box,Set.indicator_of_notMem hm]
lemma sharpWindow_prefix_integral (a : ℕ→ℂ) (N D : ℕ) :
    (∫x:ℝ,‖sharpWindow (Ioc 0 N) a (fun n=>(n:ℝ)) (D:ℝ) x‖)=
      ∑m∈range (N+D),‖cellSum a N D m‖ := by
  let F := fun x:ℝ=>‖sharpWindow (Ioc 0 N) a (fun n=>(n:ℝ)) (D:ℝ) x‖
  have hF : Integrable F := (sharpWindow_integrable _ _ _ _).norm
  have hsupport := intervalIntegral.integral_eq_integral_of_support_subset
    («μ» := volume) (sharpWindow_prefix_support a N D)
  rw [←hsupport]
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun m:ℕ=>(m:ℝ)) (n:=N+D) (fun m hm=>hF.intervalIntegrable)
  simp only [Nat.cast_zero] at hpart
  rw [←hpart]
  apply sum_congr rfl
  intro m hm
  have hle : (m:ℝ)≤((m+1:ℕ):ℝ) := by push_cast; linarith
  rw [intervalIntegral.integral_of_le hle]
  have he : (∫x in Set.Ioc (m:ℝ) ((m+1:ℕ):ℝ),F x)=
    ∫x in Set.Ioc (m:ℝ) ((m+1:ℕ):ℝ),‖cellSum a N D m‖ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact congrArg norm (sharpWindow_cell a N D m (by simpa only [Nat.cast_add,Nat.cast_one] using hx))
  rw [he]
  simp [Real.volume_real_Ioc]
lemma cellSum_norm_le {a : ℕ→ℂ} (ha : OneBounded a) (N D m : ℕ) :
    ‖cellSum a N D m‖ ≤ (D:ℝ) := by
  let S := (Finset.Ioc 0 N).filter (fun n=>n ≤ m ∧ m < n+D)
  have hsub : S⊆Ioc (m-D) m := by
    intro n hn
    obtain ⟨hn,hlo,hhi⟩ := mem_filter.mp hn
    exact mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,hlo⟩
  have hc : S.card≤D := by
    have hh := Finset.card_le_card hsub
    simp only [Nat.card_Ioc] at hh
    omega
  calc
    _ ≤ ∑n∈S,‖a n‖ := norm_sum_le _ _
    _ ≤ ∑n∈S,(1:ℝ) := sum_le_sum (fun n hn=>ha n)
    _ = (S.card:ℝ) := by simp
    _ ≤ D := by exact_mod_cast hc

end OrdinaryDiscreteWindows

end

end OAI
