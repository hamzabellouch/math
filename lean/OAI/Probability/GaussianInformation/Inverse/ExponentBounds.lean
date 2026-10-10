import Mathlib
import OAI.Probability.GaussianInformation.Inverse.StageEvents

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def positiveSum {k : ℕ} (l : Fin k → ℤ) : ℝ := ∑ i,max (l i:ℝ) 0
noncomputable def negativeSum {k : ℕ} (l : Fin k → ℤ) : ℝ := ∑ i,max (-(l i:ℝ)) 0
lemma positiveSum_nonneg {k : ℕ} (l : Fin k → ℤ) : 0 ≤ positiveSum l :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
lemma negativeSum_nonneg {k : ℕ} (l : Fin k → ℤ) : 0 ≤ negativeSum l :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
lemma sum_bins {k : ℕ} (l : Fin k → ℤ) : (∑ i,(l i:ℝ))=positiveSum l-negativeSum l := by
  rw [positiveSum,negativeSum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ (l i:ℝ)
  · simp [max_eq_left hi,max_eq_right (neg_nonpos.mpr hi)]
  · simp [max_eq_right (le_of_not_ge hi),max_eq_left (neg_nonneg.mpr (le_of_not_ge hi))]

lemma binGap_sum_le {k : ℕ} (l : Fin k → ℤ) (i : Fin k) (hl : Monotone l) :
    (∑ j,(binGap l i j:ℝ)) ≤ k*max (l i:ℝ) 0+negativeSum l := by
  calc
    _  ≤  ∑ j : Fin k,(max (l i:ℝ) 0+max (-(l j:ℝ)) 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j < i
      · have hc : ((binGap l i j:ℕ):ℤ)=l i-l j := by
          simp only [binGap,ite_eq_left hj,Int.toNat_of_nonneg (sub_nonneg.mpr (hl hj.le))]
        have hr : (binGap l i j:ℝ)=(l i:ℝ)-(l j:ℝ) := by exact_mod_cast hc
        rw [hr]
        linarith [le_max_left (l i:ℝ) 0,le_max_left (-(l j:ℝ)) 0]
      · simp only [binGap,ite_eq_right hj,Nat.cast_zero]
        positivity
    _ = _ := by simp [Finset.sum_add_distrib,negativeSum]

lemma dyadicRadius_eq_exp (l : ℤ) : dyadicRadius l=Real.exp (-(l:ℝ)*Real.log 2) := by
  rw [dyadicRadius,← Real.rpow_intCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  push_cast
  congr 1
  ring

lemma grouped_bound_eq_exp {d k : ℕ} (l : Fin k → ℤ) (i : Fin k) :
    (5:ℝ)^k*4^(∑ j,binGap l i j)*(3*dyadicRadius (l i))^(((d:ℝ)-1)/2) =
      Real.exp (k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3+
        Real.log 2*(2*(∑ j,(binGap l i j:ℝ))-(((d:ℝ)-1)/2)*(l i:ℝ))) := by
  have h5 : (5:ℝ)^k=Real.exp (k*Real.log 5) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have h4 : (4:ℝ)^(∑ j,binGap l i j)=Real.exp (Real.log 2*(2*∑ j,(binGap l i j:ℝ))) := by
    rw [← Nat.cast_sum,show Real.log 2*(2*(∑ j,binGap l i j:ℕ))=
      (∑ j,binGap l i j:ℕ)*(2*Real.log 2) by ring,Real.exp_nat_mul,
      show 2*Real.log 2=Real.log 2+Real.log 2 by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [h5,h4,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (dyadicRadius_pos _).le,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3),dyadicRadius_eq_exp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,
    ← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

noncomputable def stageExponent {d k : ℕ} (l : Fin k → ℤ) (i : Fin k) : ℝ :=
  k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3+
    Real.log 2*((2*k-(((d:ℝ)-1)/2))*max (l i:ℝ) 0+2*negativeSum l)
noncomputable def totalExponent {d k : ℕ} (l : Fin k → ℤ) : ℝ :=
  k*(k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3)+
    Real.log 2*((2*k-(((d:ℝ)-1)/2))*positiveSum l+2*k*negativeSum l)

lemma stageExponent_sum {d k : ℕ} (l : Fin k → ℤ) :
    (∑ i,stageExponent (d := d) l i)=totalExponent (d := d) l := by
  simp only [stageExponent,totalExponent,positiveSum,Finset.sum_add_distrib,← Finset.sum_mul,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma measure_stage_le {d k : ℕ} (hd : 1 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (u : Ambient d) (l : Fin k → ℤ) (hl : Monotone l) (i : Fin k)
    (f : Fin k → Ambient d) :
    ν {x | StageEvent u l i (Function.update f i x)}  ≤
      ENNReal.ofReal (Real.exp (stageExponent (d := d) l i)) := by
  have hα : 0 ≤ ((d:ℝ)-1)/2 := by
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  simp_rw [stageEvent_update]
  by_cases hi : 0 ≤ l i
  · simp only [hi,forall_true_left]
    have hm := measure_groupedTube_le ν hν u (prefixAxes (translated u f) i)
      (suborthonormal_synth_contraction (prefixAxes_suborthonormal (translated u f) i))
      (binGap l i) (dyadicRadius_pos (l i))
    apply hm.trans
    apply ENNReal.ofReal_le_ofReal
    rw [grouped_bound_eq_exp]
    apply Real.exp_le_exp.mpr
    have hir : 0 ≤ (l i:ℝ) := by exact_mod_cast hi
    unfold stageExponent
    rw [max_eq_left hir]
    have hb := binGap_sum_le l i hl
    rw [max_eq_left hir] at hb
    nlinarith
  · have hir : (l i:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hi)
    simp only [hi,false_implies,ofPred_true,measure_univ]
    have hN := negativeSum_nonneg l
    have hnon : 0 ≤ stageExponent (d := d) l i := by
      unfold stageExponent
      rw [max_eq_right hir,mul_zero,zero_add]
      positivity
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr hnon)

noncomputable def BinEvent {d k : ℕ} (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) : Set (Fin k → Ambient d) :=
  {z | Greedy residualScore (translated u z) ∧ InBins ε (translated u z) l}

lemma measurableSet_inBins {d k : ℕ} (ε : ℝ) (l : Fin k → ℤ) :
    MeasurableSet {f : Fin k → Ambient d | InBins ε f l} := by
  simp only [InBins,ofPred_forall,ofPred_and]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun f : Fin k → Ambient d => clippedLength ε f i) :=
    (measurable_gramSchmidt i).norm.max measurable_const
  exact (measurableSet_lt measurable_const hi).inter (measurableSet_le hi measurable_const)

lemma measurableSet_binEvent {d k : ℕ} (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) :
    MeasurableSet (BinEvent ε u l) :=
  (measurableSet_greedy.inter (measurableSet_inBins ε l)).preimage (measurable_translated u)

lemma measure_binEvent_le {d k : ℕ} (hd : 1 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) :
    (Measure.pi (fun _ : Fin k => ν)) (BinEvent ε u l)  ≤
      ENNReal.ofReal (Real.exp (totalExponent (d := d) l)) := by
  classical
  by_cases hl : Monotone l
  · calc
      _  ≤  (Measure.pi (fun _ : Fin k => ν)) {z | ∀ i,StageEvent u l i z} := by
        apply measure_mono
        intro z hz
        exact greedy_bins_stageEvents u hz.1 hz.2
      _  ≤  ∏ i,ENNReal.ofReal (Real.exp (stageExponent (d := d) l i)) :=
        measure_sequential_event_le ν u k (StageEvent u l) _ (measurableSet_stageEvent u l)
          (stageEvent_prefix u l) (measure_stage_le hd ν hν u l hl)
      _ = ENNReal.ofReal (Real.exp (totalExponent (d := d) l)) := by
        rw [← stageExponent_sum l,Real.exp_sum]
        exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)).symm
  · have he : BinEvent ε u l=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hl (bins_monotone hz.1 hz.2)
    simp [he]

end AllScaleInverseVolume

end OAI
