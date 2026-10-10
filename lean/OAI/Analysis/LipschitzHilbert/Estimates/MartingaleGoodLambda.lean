import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleLocalMaximal
import OAI.Analysis.LipschitzHilbert.Estimates.FirstExceed

namespace OAI

/-! A first-crossing contraction for a finite martingale with bounded
conditional mean oscillation. This is the finite stopping step in the
John--Nirenberg proof; no exponential-tail theorem is assumed. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

def TerminalMeanOscillationBound (F : ℕ → X → ℝ) (ℱ : Filtration ℕ m)
    (μ : Measure X) (N : ℕ) (A : ℝ) : Prop :=
  ∀ n ≤ N, ∀ s, MeasurableSet[ℱ n] s →
    (∫ x in s, |F N x - F n x| ∂μ) ≤ A * μ.real s

theorem martingale_goodLambda (hF : Martingale F ℱ μ) (N : ℕ)
    {A D lambda : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hlambda : 0 ≤ lambda)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + 2 * A) N) ≤
      (1 / 2 : ℝ) * μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) lambda N) := by
  let U := fun i x => ‖F i x - F 0 x‖
  let B := fun n => firstExceed U lambda n
  have hUm (i : ℕ) : Measurable (U i) :=
    ((hF.stronglyMeasurable i).measurable.le (ℱ.le i)).sub
      ((hF.stronglyMeasurable 0).measurable.le (ℱ.le 0)) |>.norm
  have hBm (n : ℕ) : MeasurableSet[ℱ n] (B n) := by
    let : MeasurableSpace X := ℱ n
    apply measurableSet_firstExceed U lambda n
    intro i hi
    exact ((hF.stronglyMeasurable i).mono (ℱ.mono hi)).measurable.sub
      ((hF.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le n))).measurable |>.norm
  have hcell (n : Fin (N + 1)) :
      μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) ≤
        (1 / 2 : ℝ) * μ.real (B n) := by
    let S := {x | ∃ i ≤ N - n.val, 2 * A ≤ |F (n.val + i) x - F n x|}
    have hSm : MeasurableSet S := by
      change MeasurableSet {x | ∃ i, i ≤ N - n.val ∧ 2 * A ≤ |F (n.val + i) x - F n x|}
      simp only [ofPred_exists, ofPred_and]
      apply MeasurableSet.iUnion
      intro i
      have hd : Measurable (fun x => F (n.val + i) x - F n x) :=
        ((hF.stronglyMeasurable (n.val + i)).measurable.le (ℱ.le _)).sub
          ((hF.stronglyMeasurable n.val).measurable.le (ℱ.le _))
      simpa only [Real.norm_eq_abs] using
        (MeasurableSet.const (i ≤ N - n.val)).inter
          (measurableSet_le measurable_const hd.norm)
    have hlocal := martingale_local_maximal_L1 hF n.val (N - n.val) (hBm n) (by positivity : 0 < 2 * A)
    have hbudget := hBMO n.val (by omega) (B n) (hBm n)
    have hindex : n.val + (N - n.val) = N := by omega
    rw [hindex] at hlocal
    have hsub : finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n ⊆ S ∩ B n := by
      simpa only [S, U, B, Real.norm_eq_abs] using
        firstExceed_large_subset F N n.val (by omega) hlambda hD
          (by positivity : 0 ≤ 2 * A) hjump
    calc
      _ ≤ μ.real (S ∩ B n) := measureReal_mono hsub
      _ = (μ.restrict (B n)).real S := (measureReal_restrict_apply hSm).symm
      _ ≤ (2 * A)⁻¹ * ∫ x in B n, |F N x - F n x| ∂μ := hlocal
      _ ≤ (2 * A)⁻¹ * (A * μ.real (B n)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by field_simp [hA.ne']
  have hcover : finiteMaxEvent U (lambda + D + 2 * A) N ⊆
      ⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n := by
    intro x hx
    obtain ⟨i,hi,hUi⟩ := hx
    have hxsmall : x ∈ finiteMaxEvent U lambda N := ⟨i,hi,by linarith⟩
    rw [← firstExceed_union] at hxsmall
    obtain ⟨n,hn⟩ := mem_iUnion.mp hxsmall
    exact mem_iUnion.mpr ⟨n,⟨i,hi,hUi⟩,hn⟩
  calc
    _ ≤ μ.real (⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_mono hcover
    _ ≤ ∑ n : Fin (N + 1), μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (N + 1), (1 / 2 : ℝ) * μ.real (B n) := Finset.sum_le_sum (fun n _ => hcell n)
    _ = (1 / 2 : ℝ) * μ.real (finiteMaxEvent U lambda N) := by
      rw [← Finset.mul_sum, firstExceed_measure_sum μ U lambda N (fun i _ => hUm i)]

end LipschitzHilbert

end

end OAI
