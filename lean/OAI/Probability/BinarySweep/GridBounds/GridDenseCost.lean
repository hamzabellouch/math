import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridSplitCost

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma sum_row_holes : ∑y, Fintype.card (RowLabels bits H y)=h := by
  rw [←Fintype.card_sigma]
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv (fun k : Fin h => rightSlot bits (H.position 0 k)))
  exact he.trans (Fintype.card_fin h)

lemma sum_column_holes : ∑x, Fintype.card (ColumnLabels bits H x)=h := by
  rw [←Fintype.card_sigma]
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => leftSlot bits (H.position (rightTime (m:=m) 0) k)))
  exact he.trans (Fintype.card_fin h)

lemma child_error_sum (e : ℝ) :
    (∑y, (e*Fintype.card (RowLabels bits H y)*Real.log (gridSize (leftBits bits))-
      pathCost (rowFamily bits H y)))+
    (∑x, (e*Fintype.card (ColumnLabels bits H x)*Real.log (gridSize (rightBits bits))-
      pathCost (columnFamily bits H x)))=
      e*h*Real.log (gridSize bits)-pathCost H := by
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum,
    ←Finset.sum_mul,←Finset.mul_sum,←Nat.cast_sum,←Nat.cast_sum,
    sum_row_holes,sum_column_holes,pathCost_split,size_split,Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (gridSize_pos (leftBits bits)).ne')
      (by exact_mod_cast (gridSize_pos (rightBits bits)).ne')]
  ring

lemma blockLogSize_le {I : Type*} [Fintype I] (f : I → ℕ) (s : ℕ) (hf : ∀i, f i ≤ s) :
    blockLogSize f ≤ Fintype.card I*Real.log (s+1:ℝ) := by
  calc
    _ ≤ ∑_i : I, Real.log (s+1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hf i) 1)
    _ = _ := by simp

lemma blocksLog_le :
    blockLogSize (rowFreeSize bits H)+blockLogSize (columnFreeSize bits H)≤
      (gridSize (rightBits bits):ℝ)*Real.log (gridSize (leftBits bits)+1:ℝ)+
      (gridSize (leftBits bits):ℝ)*Real.log (gridSize (rightBits bits)+1:ℝ) := by
  have hr := blockLogSize_le (rowFreeSize bits H) (gridSize (leftBits bits)) (fun _ => by
    rw [rowFreeSize,card_freeSlot]
    exact Nat.sub_le _ _)
  have hc := blockLogSize_le (columnFreeSize bits H) (gridSize (rightBits bits)) (fun _ => by
    rw [columnFreeSize,card_freeSlot]
    exact Nat.sub_le _ _)
  simpa only [card_gridSlot] using add_le_add hr hc

theorem conditional_hook_with_cost {t : ℕ} (ht : 0<t)
    (α : (junctionSize bits H).Partition) (hα : Young.InHook (Young.diagram α) t)
    (z : ℝ) {q : ℕ} (hq : 0<q) (c e : ℝ) (hc : 0≤c) (hcq : c≤q)
    (hchildR : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y)))
    (hchildC : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) :
    evenMoment q (groupAverage ((Young.partitionHilbertRep α).comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-c*typeF α+e*h*Real.log (gridSize bits)-pathCost H+c*h+
        (1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2*
          ((gridSize (rightBits bits):ℝ)*Real.log (gridSize (leftBits bits)+1:ℝ)+
           (gridSize (leftBits bits):ℝ)*Real.log (gridSize (rightBits bits)+1:ℝ))) := by
  have hr : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+(e*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) := by
    intros; simpa only [add_sub_assoc] using hchildR _ _
  have hc' : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+(e*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) := by
    intros; simpa only [add_sub_assoc] using hchildC _ _
  refine (conditional_hook_dense_bound bits H ht α hα z hq c hc hcq _ _ hr hc').trans ?_
  apply Real.exp_le_exp.mpr
  rw [add_assoc (-c*typeF α),child_error_sum]
  have hb := mul_le_mul_of_nonneg_left (blocksLog_le bits H)
    (by positivity : 0≤(1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2)
  linarith

end BinaryCoordinateSweeps.GridSplit

end

open Filter Asymptotics
open scoped Topology

namespace BinaryCoordinateSweeps

def inductionGap (s : ℝ) : ℝ := 1 / (20 * Real.sqrt (Real.log s))

lemma dense_error_eventually : ∀ᶠ s : ℝ in atTop,
    s ^ (9/10 : ℝ) + s ^ (199/200 : ℝ) * Real.log s ≤
      inductionGap s * s ^ (399/400 : ℝ) := by
  have ho := isLittleO_log_rpow_rpow_atTop (3/2 : ℝ) (by norm_num : (0 : ℝ) < 1/400)
  have he := ho.bound (by norm_num : (0 : ℝ) < 1/40)
  filter_upwards [he, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with s hs hl h1
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one h1
  have hl0 : 0 < Real.log s := lt_of_lt_of_le zero_lt_one hl
  have ht : (Real.log s) ^ (3/2 : ℝ) ≤ (1/40 : ℝ) * s ^ (1/400 : ℝ) := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _)] using hs
  have hl32 : Real.sqrt (Real.log s) * Real.log s = (Real.log s) ^ (3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (Real.log s) ^ (1/2 : ℝ) * Real.log s =
          (Real.log s) ^ (1/2 : ℝ) * (Real.log s) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log s) ^ (3/2 : ℝ) := by rw [← Real.rpow_add hl0]; norm_num
  have hpow : s ^ (9/10 : ℝ) ≤ s ^ (199/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have hpow0 : 0 ≤ s ^ (199/200 : ℝ) := Real.rpow_nonneg hs0.le _
  have hsq0 : 0 < Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hl0
  unfold inductionGap
  rw [div_mul_eq_mul_div, one_mul]
  apply (le_div_iff₀ (by positivity : 0 < 20 * Real.sqrt (Real.log s))).mpr
  calc
    (s ^ (9/10 : ℝ) + s ^ (199/200 : ℝ) * Real.log s) *
        (20 * Real.sqrt (Real.log s)) ≤
        (2 * s ^ (199/200 : ℝ) * Real.log s) * (20 * Real.sqrt (Real.log s)) := by
      gcongr
      nlinarith
    _ = 40 * s ^ (199/200 : ℝ) * (Real.log s) ^ (3/2 : ℝ) := by
      rw [← hl32]
      ring
    _ ≤ 40 * s ^ (199/200 : ℝ) * ((1/40 : ℝ) * s ^ (1/400 : ℝ)) := by gcongr
    _ = s ^ (399/400 : ℝ) := by
      rw [show 40 * s ^ (199/200 : ℝ) * ((1/40 : ℝ) * s ^ (1/400 : ℝ)) =
        s ^ (199/200 : ℝ) * s ^ (1/400 : ℝ) by ring, ← Real.rpow_add hs0]
      norm_num

theorem dense_induction_absorption_eventually (C : ℝ) : ∀ᶠ s : ℕ in atTop,
    ∀ b h k F G J : ℝ, 0 ≤ h → 0 ≤ k → 0 ≤ J →
      Real.log 4 * b ≤ (1/1000 : ℝ) * Real.log s →
      F ≤ G + k * Real.log s →
      (s : ℝ) ^ (399/400 : ℝ) ≤ F →
      ((s : ℝ) ^ (199/200 : ℝ) ≤ k →
        k * ((1/200 : ℝ) * Real.log s - C) ≤ J) →
      -(cExponent s + inductionGap s) * G +
        (eExponent s - inductionGap s) * (h+k) * Real.log s +
        (s : ℝ) ^ (9/10 : ℝ) + Real.log 4 * k * b - J ≤
        -cExponent s * F + eExponent s * h * Real.log s := by
  have hlim : Tendsto (fun s : ℕ => (s : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hloglim := Real.tendsto_log_atTop.comp hlim
  filter_upwards [hlim.eventually dense_error_eventually,
      hloglim.eventually_ge_atTop (max 1 (1000*C))] with s herr hlarge
  have hl : 1 ≤ Real.log s := (le_max_left _ _).trans hlarge
  have hC : 1000*C ≤ Real.log s := (le_max_right _ _).trans hlarge
  have hl0 : 0 < Real.log s := by linarith
  have hg0 : 0 < inductionGap s := by unfold inductionGap; positivity
  have hc0 : 0 ≤ cExponent s + inductionGap s := by unfold cExponent c0; positivity
  intro b h k F G J hh hk hJ hb hdim hF hremoved
  have hce : cExponent s + inductionGap s + (eExponent s - inductionGap s) =
      (1/5000 : ℝ) := by unfold cExponent eExponent c0 e0; ring
  have hextra : (1/5000 : ℝ) * k * Real.log s + Real.log 4 * k * b - J ≤
      (s : ℝ) ^ (199/200 : ℝ) * Real.log s := by
    by_cases hbig : (s : ℝ) ^ (199/200 : ℝ) ≤ k
    · have hpay := hremoved hbig
      have hb' := mul_le_mul_of_nonneg_left hb hk
      have hcost : (1/5000 : ℝ) * k * Real.log s + Real.log 4 * k * b - J ≤ 0 := by
        have hcoef : (1/5000 : ℝ) * Real.log s + (1/1000 : ℝ) * Real.log s ≤
            (1/200 : ℝ) * Real.log s - C := by nlinarith
        have hcoef' := mul_le_mul_of_nonneg_left hcoef hk
        nlinarith
      exact hcost.trans (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg s) _) hl0.le)
    · have hk' : k ≤ (s : ℝ) ^ (199/200 : ℝ) := (lt_of_not_ge hbig).le
      have hb' := mul_le_mul_of_nonneg_left hb hk
      have hkl := mul_le_mul_of_nonneg_right hk' hl0.le
      have hkl0 := mul_nonneg hk hl0.le
      nlinarith
  have hce' := congrArg (fun t : ℝ => t * k * Real.log s) hce
  have hdim' := mul_le_mul_of_nonneg_left hdim hc0
  have hsave := mul_le_mul_of_nonneg_left hF hg0.le
  have hholes := mul_nonneg (mul_nonneg hg0.le hh) hl0.le
  nlinarith

end BinaryCoordinateSweeps

end

end OAI
