import Mathlib
import OAI.Probability.Perceptron.Variational.BackwardScore
import OAI.Probability.Perceptron.Variational.CoupledDual

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma Jet3.eq_of_f_eq {g h : Jet3} (he : g.f=h.f) : g=h := by
  have h1 : g.d1=h.d1 := by
    ext x
    rw [← g.deriv_eq,← h.deriv_eq,he]
  have h2 : g.d2=h.d2 := by
    ext x
    rw [← g.deriv2_eq,← h.deriv2_eq,he]
  have h3 : g.d3=h.d3 := by
    ext x
    rw [← g.deriv3_eq,← h.deriv3_eq,he]
  cases g
  cases h
  simp_all

lemma Jet3.heatLog_zero_time (g : Jet3) (d : ℝ≥0) : g.heatLog 0 d=g := by
  apply Jet3.eq_of_f_eq
  ext x
  simp only [Jet3.heatLog_f,heatLogBCF_coe,heatLog_zero]

def finiteStepControlJet (g : Jet3) : (n : ℕ)→(Fin (n+1)→Time)→(Fin n→ℝ≥0)→Jet3
  | 0,_,_ => g
  | n+1,q,d => (finiteStepControlJet g n (fun i => q i.succ) (fun i => d i.succ)).heatLog
      (timeSpan (q 0) (q 1)) (d 0)

lemma finiteStepControlJet_chain (g : Jet3) (m : Trial) (n : ℕ)
    (q : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q)
    (hm : ∀ i : Fin n, ∀ r∈Ioc (q i.castSucc) (q i.succ), m r=(d i:ℝ)) :
    HeatChain m g (q 0) (q (Fin.last n)) (finiteStepControlJet g n q d) := by
  induction n with
  | zero => exact HeatChain.nil (q 0)
  | succ n ih =>
    have ih' := ih (fun i => q i.succ) (fun i => d i.succ)
      (hq.comp (Fin.strictMono_succ.monotone)) (fun i => hm i.succ)
    change HeatChain m g (q 1) (q (Fin.last (n+1))) _ at ih'
    have h01 : q 0≤q 1 := hq (Fin.zero_le _)
    rcases lt_or_eq_of_le h01 with hlt | he
    · exact HeatChain.cons (d 0) hlt (hq (Fin.le_last _)) (hm 0) ih'
    · simpa only [finiteStepControlJet,he,timeSpan,sub_self,Real.toNNReal_zero,
        Jet3.heatLog_zero_time] using ih'

lemma finiteStepControlJet_value (g : Jet3) (m : Trial) (n : ℕ)
    (q : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (hm : ∀ i : Fin n, ∀ r∈Ioc (q i.castSucc) (q i.succ), m r=(d i:ℝ))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f m=(finiteStepControlJet g n q d).f 0 := by
  have H := finiteStepControlJet_chain g m n q d hq hm
  rw [hq0,hq1] at H
  exact H.controlValue_eq P hB

def leftWeightedStepTrial {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) : Trial where
  toFun := fun t => ∑ i, if q i<t then w i else 0
  monotone := by
    intro s t hst
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i<s
    · simp only [ite_eq_left hi,ite_eq_left (hi.trans_le hst),le_refl]
    · rw [ite_eq_right hi]
      split_ifs <;> first | exact hw i | rfl
  measurable := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const
  nonneg := by
    intro t
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  le_one := by
    intro t
    rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | rfl | exact hw i

lemma leftWeightedStepTrial_ae {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    (leftWeightedStepTrial w q hw hw1 : Time→ℝ)=ᵐ[timeLaw] weightedStepTrial w q hw hw1 := by
  have he : ∀ᵐ t ∂timeLaw, ∀ i, t≠q i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_iff.mpr
    simp
  filter_upwards [he] with t ht
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i≤t
  · rw [ite_eq_left hi,ite_eq_left (lt_of_le_of_ne hi (Ne.symm (ht i)))]
  · rw [ite_eq_right hi,ite_eq_right (not_lt_of_ge (le_of_not_ge hi))]

def weightedControlCoefficient (n : ℕ) (w : Fin (n+1)→ℝ) (hw : ∀ i, 0≤w i)
    (i : Fin n) : ℝ≥0 :=
  ⟨∑ j : Fin (n+1), if j ≤ i.castSucc then w j else 0,Finset.sum_nonneg fun j _ => by
    split_ifs <;> first | exact hw j | rfl⟩

lemma leftWeightedStepTrial_interval (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (i : Fin n) {r : Time} (hr : r∈Ioc (q i.castSucc) (q i.succ)) :
    leftWeightedStepTrial w q hw hw1 r=(weightedControlCoefficient n w hw i:ℝ) := by
  change (∑ j, if q j<r then w j else 0) = ∑ j, if j ≤ i.castSucc then w j else 0
  apply Finset.sum_congr rfl
  intro j _
  have he : q j<r ↔ j ≤ i.castSucc := by
    constructor
    · intro hj
      by_contra hn
      have hij : i.succ ≤ j := by
        simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hn ⊢
        omega
      exact not_lt_of_ge ((hq hij).trans' hr.2) hj
    · intro hj
      exact (hq hj).trans_lt hr.1
  simp only [he]

theorem weightedStepTrial_controlValue (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      (finiteStepControlJet g n q (weightedControlCoefficient n w hw)).f 0 := by
  have he := leftWeightedStepTrial_ae w q hw hw1
  have hv := controlValue_trial_abs_sub_le P g.f (weightedStepTrial w q hw hw1)
    (leftWeightedStepTrial w q hw hw1) ‖g.d1‖₊ g.lipschitz
  have hz : (∫ t, |weightedStepTrial w q hw hw1 t-leftWeightedStepTrial w q hw hw1 t| ∂timeLaw)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with t ht
    simp only [ht,sub_self,abs_zero,Pi.zero_apply]
  rw [hz,mul_zero] at hv
  have hv' := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))
  rw [hv']
  exact finiteStepControlJet_value g _ n q (weightedControlCoefficient n w hw) hq hq0 hq1
    (fun i r hr => leftWeightedStepTrial_interval n w q hw hw1 hq i hr) P hB

def paddedControlNodes {n : ℕ} (q : Fin (n+1)→Time) : Fin (n+3)→Time :=
  Fin.cons 0 (Fin.snoc q 1)

def paddedControlWeights {n : ℕ} (w : Fin (n+1)→ℝ) : Fin (n+3)→ℝ :=
  Fin.cons 0 (Fin.snoc w 0)

lemma paddedControlWeights_nonneg {n : ℕ} (w : Fin (n+1)→ℝ) (hw : ∀ i, 0≤w i) :
    ∀ i, 0≤paddedControlWeights w i := by
  intro i
  refine Fin.cases (by simp [paddedControlWeights]) (fun j => ?_) i
  change 0≤(Fin.snoc w 0 : Fin (n+2)→ℝ) j
  refine Fin.lastCases (by simp) (fun l => ?_) j
  simpa using hw l

lemma paddedControlWeights_sum {n : ℕ} (w : Fin (n+1)→ℝ) (hw1 : ∑ i, w i=1) :
    ∑ i, paddedControlWeights w i=1 := by
  unfold paddedControlWeights
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,zero_add]
  rw [Fin.sum_univ_castSucc]
  simpa using hw1

lemma paddedControlNodes_mono {n : ℕ} (q : Fin (n+1)→Time) (hq : Monotone q) :
    Monotone (paddedControlNodes q) := by
  have hs : Monotone (Fin.snoc q 1) := by
    simpa only [Fin.insertNth_last'] using Fin.insertNth_last_monotone hq 1 (show q (Fin.last n)≤1 from le_top)
  simpa only [Fin.insertNth_zero',paddedControlNodes] using
    Fin.insertNth_zero_monotone hs 0 (show (0:Time)≤(Fin.snoc q 1 : Fin (n+2)→Time) 0 from bot_le)

lemma paddedControlTrial_eq {n : ℕ} (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    weightedStepTrial (paddedControlWeights w) (paddedControlNodes q)
      (paddedControlWeights_nonneg w hw) (paddedControlWeights_sum w hw1)=
        weightedStepTrial w q hw hw1 := by
  apply Trial.ext_fun
  intro t
  change (∑ i, if paddedControlNodes q i≤t then paddedControlWeights w i else 0)=
    ∑ i, if q i≤t then w i else 0
  unfold paddedControlNodes paddedControlWeights
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,ite_self,zero_add]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,ite_self,add_zero]

theorem sourceWeightedTrial_controlValue (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      (finiteStepControlJet g (n+2) (paddedControlNodes q)
        (weightedControlCoefficient (n+2) (paddedControlWeights w) (paddedControlWeights_nonneg w hw))).f 0 := by
  rw [← paddedControlTrial_eq w q hw hw1]
  exact weightedStepTrial_controlValue (n+2) _ _ (paddedControlWeights_nonneg w hw)
    (paddedControlWeights_sum w hw1) (paddedControlNodes_mono q hq)
    (by simp [paddedControlNodes]) (by simp [paddedControlNodes]) g P hB

end SphericalPerceptronFreeEnergy
end

end OAI
