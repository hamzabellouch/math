import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
noncomputable section

def Whp (β : ℝ) (P : ∀n,Disorder n→Prop) : Prop :=
  Tendsto (fun n=>disorderLaw β n {g | ¬P n g}) atTop (𝓝 0)

lemma whp_iff_real (β : ℝ) (P : ∀n,Disorder n→Prop) :
    Whp β P ↔ Tendsto (fun n=>(disorderLaw β n).real {g | ¬P n g}) atTop (𝓝 0) := by
  let (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by unfold disorderLaw; infer_instance
  constructor
  · intro h
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h
  · intro h
    have H:=(ENNReal.continuous_ofReal.tendsto 0).comp h
    change Tendsto (fun n=>disorderLaw β n {g | ¬P n g}) atTop (𝓝 0)
    simpa only [Function.comp_def,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_zero] using H

lemma Whp.mono {β : ℝ} {P Q : ∀n,Disorder n→Prop} (hP : Whp β P)
    (hPQ : ∀ᶠ n : ℕ in atTop,∀g,P n g→Q n g) : Whp β Q := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hP
    (Eventually.of_forall (fun _=>bot_le))
  filter_upwards [hPQ] with n hn
  apply measure_mono
  intro g hg hp
  exact hg (hn g hp)

lemma Whp.of_eventually {β : ℝ} {P : ℕ→Prop} (hP : ∀ᶠ n : ℕ in atTop,P n) :
    Whp β (fun n _=>P n) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hP] with n hn
  simp [hn]

lemma Whp.and {β : ℝ} {P Q : ∀n,Disorder n→Prop} (hP : Whp β P) (hQ : Whp β Q) :
    Whp β (fun n g=>P n g ∧ Q n g) := by
  classical
  have H:=hP.add hQ
  rw [add_zero] at H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
    (Eventually.of_forall (fun _=>bot_le))
  apply Eventually.of_forall
  intro n
  have he : {g:Disorder n | ¬(P n g ∧ Q n g)}={g | ¬P n g}∪{g | ¬Q n g} := by
    ext g
    simp only [mem_ofPred_eq,mem_union]
    tauto
  rw [he]
  exact measure_union_le _ _

lemma whp_finset {β : ℝ} {ι : Type*} (s : Finset ι) (P : ι→∀n,Disorder n→Prop)
    (hP : ∀i∈s,Whp β (P i)) : Whp β (fun n g=>∀i∈s,P i n g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply Whp.mono (Whp.of_eventually (β:=β) (P:=fun _=>True) (Eventually.of_forall (fun _=>True.intro)))
    exact Eventually.of_forall (fun n g _=>by simp)
  | @insert i s hi ih =>
    have H := (hP i (by simp)).and (ih (fun j hj=>hP j (by simp [hj])))
    exact H.mono (Eventually.of_forall (fun n g hg=>by simpa only [Finset.mem_insert,forall_eq_or_imp] using hg))

lemma whp_forall_lt {β : ℝ} (r : ℕ) (P : ℕ→∀n,Disorder n→Prop)
    (hP : ∀k<r,Whp β (P k)) : Whp β (fun n g=>∀k<r,P k n g) := by
  simpa only [Finset.mem_range] using whp_finset (Finset.range r) P (by simpa only [Finset.mem_range] using hP)

lemma whp_full_probability {β : ℝ} {P : ∀n,Disorder n→Prop} (hP : Whp β P) :
    Tendsto (fun n=>disorderLaw β n {g | P n g}) atTop (𝓝 1) := by
  classical
  let (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by unfold disorderLaw; infer_instance
  have H := (whp_iff_real β P).mp hP
  have H' := (tendsto_const_nhds (x:=(1:ℝ))).sub H
  rw [sub_zero] at H'
  have ht : Tendsto (fun n=>(disorderLaw β n).real {g | P n g}) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le H' tendsto_const_nhds
    · intro n
      have hs := measureReal_union_le (μ:=disorderLaw β n) {g | P n g} {g | ¬P n g}
      have he : ({g:Disorder n | P n g}∪{g | ¬P n g})=univ := by
        ext g
        simp only [mem_ofPred_eq,mem_union,mem_univ]
        tauto
      rw [he,probReal_univ] at hs
      linarith
    · intro n
      exact measureReal_le_one
  have hh:=(ENNReal.continuous_ofReal.tendsto 1).comp ht
  simpa only [Function.comp_def,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_one] using hh

end
end SKGap.FullMain

end OAI
