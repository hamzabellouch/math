import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CellSum

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
lemma cellSum_full (a : ℕ→ℂ) (N D y : ℕ) (hy : y+D≤N) :
    cellSum a N D (D+y)=∑k∈range D,a (y+1+k) := by
  have he : (Finset.Ioc 0 N).filter (fun n=>n ≤ D+y ∧ D+y < n+D)=
      Finset.Ico (y+1) (y+D+1) := by
    ext n
    simp only [mem_filter,Finset.mem_Ioc,Finset.mem_Ico]
    omega
  unfold cellSum
  rw [he,sum_Ico_eq_sum_range]
  have hl : y+D+1-(y+1)=D := by omega
  rw [hl]
lemma prefix_l1_le_short_norm {a : ℕ→ℂ} (ha : OneBounded a) (N D : ℕ) :
    (∫x:ℝ,‖sharpWindow (Ioc 0 N) a (fun n=>(n:ℝ)) (D:ℝ) x‖) ≤
      (∑y∈range N,‖∑k∈range D,a (y+1+k)‖)+2*(D:ℝ)^2 := by
  classical
  rw [sharpWindow_prefix_integral]
  have he : N+D=D+N := by omega
  rw [he,sum_range_add]
  have hhead : (∑m∈range D,‖cellSum a N D m‖) ≤ (D:ℝ)^2 := by
    calc
      _ ≤ ∑m∈range D,(D:ℝ) := sum_le_sum (fun m hm=>cellSum_norm_le ha N D m)
      _ = _ := by simp; ring
  let S := (range N).filter (fun y=>N<D+y)
  have hsub : S⊆Ico (N-D) N := by
    intro y hy
    have hh := mem_filter.mp hy
    exact mem_Ico.mpr ⟨by have := hh.2; omega,mem_range.mp hh.1⟩
  have hc : S.card≤D := by
    have hh := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hh
    omega
  have hbound (y : ℕ) : ‖cellSum a N D (D+y)‖ ≤
      ‖∑k∈range D,a (y+1+k)‖ + if N<D+y then (D:ℝ) else 0 := by
    by_cases hy : N<D+y
    · rw [ite_eq_left hy]
      exact (cellSum_norm_le ha N D (D+y)).trans (le_add_of_nonneg_left (norm_nonneg _))
    · rw [ite_eq_right hy,add_zero,cellSum_full a N D y (by omega)]
  have htail : (∑y∈range N,‖cellSum a N D (D+y)‖) ≤
      (∑y∈range N,‖∑k∈range D,a (y+1+k)‖)+(D:ℝ)^2 := by
    calc
      _ ≤ ∑y∈range N,(‖∑k∈range D,a (y+1+k)‖+if N<D+y then (D:ℝ) else 0) :=
        sum_le_sum (fun y hy=>hbound y)
      _ = (∑y∈range N,‖∑k∈range D,a (y+1+k)‖)+(S.card:ℝ)*D := by
        rw [sum_add_distrib,←sum_filter]
        simp only [S,sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply _root_.add_le_add (le_refl _)
        have hr : (S.card:ℝ)≤D := by exact_mod_cast hc
        nlinarith only [mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg D)]
  linarith only [hhead,htail]

end OrdinaryDiscreteWindows

end

end OAI
