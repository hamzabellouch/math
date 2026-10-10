import Mathlib
import OAI.Probability.Perceptron.Variational.UpperContact

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def trialLevelQuantile (m : Trial) (n : ℕ) (i : Fin (n+1)) : Time :=
  sInf {t : Time | (i:ℝ)/(n+1:ℝ)< m t}

lemma trialLevelQuantile_mono (m : Trial) (n : ℕ) : Monotone (trialLevelQuantile m n) := by
  intro i j hij
  apply le_sInf
  intro t ht
  apply sInf_le
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right
    (show (i:ℝ) ≤ (j:ℝ) by exact_mod_cast hij) (by positivity : (0:ℝ)≤n+1)) ht

lemma trialLevelQuantile_le (m : Trial) (n : ℕ) (i : Fin (n+1)) {t : Time}
    (ht : (i:ℝ)/(n+1:ℝ)< m t) : trialLevelQuantile m n i≤t := sInf_le ht

lemma trialLevelQuantile_lt (m : Trial) (n : ℕ) (i : Fin (n+1)) {t : Time}
    (ht : trialLevelQuantile m n i<t) : (i:ℝ)/(n+1:ℝ)< m t := by
  obtain ⟨s,hs,hst⟩ := sInf_lt_iff.mp ht
  exact hs.trans_le (m.monotone hst.le)

lemma uniform_threshold_sum (m : Trial) (n : ℕ) (t : Time) :
    (∑ i : Fin (n+1), if (i:ℝ)/(n+1:ℝ)< m t then (1/(n+1:ℝ)) else 0)=
      upperRoundedTrial m n t := by
  have hc : ⌈(n+1:ℝ)*m t⌉₊≤n+1 := Nat.ceil_le.mpr (by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith [m.le_one t])
  have he (i : ℕ) : ((i:ℝ)/(n+1:ℝ)< m t) ↔ i<⌈(n+1:ℝ)*m t⌉₊ := by
    rw [div_lt_iff₀ (by positivity),Nat.lt_ceil]
    rw [mul_comm]
  simp_rw [he]
  change (∑ i : Fin (n+1), (fun j : ℕ => if j<⌈(n+1:ℝ)*m t⌉₊ then 1/(n+1:ℝ) else 0) i.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j<⌈(n+1:ℝ)*m t⌉₊ then 1/(n+1:ℝ) else 0) (n+1),←Finset.sum_filter]
  have hset : (Finset.range (n+1)).filter (fun i => i<⌈(n+1:ℝ)*m t⌉₊)=
      Finset.range ⌈(n+1:ℝ)*m t⌉₊ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hset,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  change _=(⌈((n+1:ℕ):ℝ)*m t⌉₊:ℝ)/(n+1:ℕ)
  simp only [Nat.cast_add,Nat.cast_one]
  ring

def levelStepTrial (m : Trial) (n : ℕ) : Trial :=
  weightedStepTrial (fun _ : Fin (n+1) => 1/(n+1:ℝ)) (trialLevelQuantile m n)
    (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n)

lemma le_levelStepTrial (m : Trial) (n : ℕ) (t : Time) : m t≤levelStepTrial m n t := by
  apply (le_upperRoundedTrial m n t).trans
  rw [←uniform_threshold_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : (i:ℝ)/(n+1:ℝ)< m t
  · simp only [ite_eq_left hi,ite_eq_left (trialLevelQuantile_le m n i hi),le_refl]
  · rw [ite_eq_right hi]
    split_ifs <;> positivity

lemma levelStepTrial_ae (m : Trial) (n : ℕ) :
    (fun t => levelStepTrial m n t)=ᵐ[timeLaw] (fun t => upperRoundedTrial m n t) := by
  have hn : ∀ᵐ t ∂timeLaw, ∀ i : Fin (n+1), t≠trialLevelQuantile m n i := by
    apply ae_all_iff.mpr
    intro i
    simp [ae_iff,timeLaw_eq_volume]
  filter_upwards [hn] with t ht
  rw [←uniform_threshold_sum]
  change (∑ i : Fin (n+1), if trialLevelQuantile m n i≤t then 1/(n+1:ℝ) else 0)=_
  apply Finset.sum_congr rfl
  intro i _
  have hi : trialLevelQuantile m n i≤t ↔ (i:ℝ)/(n+1:ℝ)< m t :=
    ⟨fun h => trialLevelQuantile_lt m n i (lt_of_le_of_ne h (Ne.symm (ht i))),trialLevelQuantile_le m n i⟩
  simp only [hi]

lemma levelStepTrial_L1 (m : Trial) (n : ℕ) :
    (∫ t, |levelStepTrial m n t-m t| ∂timeLaw)≤1/(n+1:ℝ) := by
  have he : (∫ t, |levelStepTrial m n t-m t| ∂timeLaw)=
      ∫ t, |upperRoundedTrial m n t-m t| ∂timeLaw :=
    integral_congr_ae ((levelStepTrial_ae m n).mono fun t ht => by dsimp only at ht ⊢; rw [ht])
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_one] using upperRoundedTrial_L1_le m n

lemma trialLevelQuantile_terminal (m : Trial) (n : ℕ) {r : Time} (hr : m r=1)
    (i : Fin (n+1)) : trialLevelQuantile m n i≤r := by
  apply trialLevelQuantile_le
  rw [hr]
  apply (div_lt_one (by positivity : (0:ℝ)<n+1)).mpr
  exact_mod_cast i.isLt

theorem exists_uniform_step_trial_approx (m : Trial) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (q : Fin (n+1)→Time), Monotone q ∧ (q (Fin.last n):ℝ)<1 ∧
      let v := weightedStepTrial (fun _ : Fin (n+1) => 1/(n+1:ℝ)) q
        (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n)
      (∀ t, m t≤v t) ∧ entropy v≤entropy m ∧
        (∫ t, |v t-m t| ∂timeLaw)<ε := by
  obtain ⟨u,hufin,⟨r,hr,hterm⟩,hmu,hS,_,hL⟩ :=
    exists_finite_terminal_trial_approx m (show 0<ε/2 by positivity)
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0<ε/2 by positivity)
  refine ⟨n,trialLevelQuantile u n,trialLevelQuantile_mono u n,
    lt_of_le_of_lt (trialLevelQuantile_terminal u n (hterm r le_rfl) _) hr,?_⟩
  change (∀ t, m t≤levelStepTrial u n t) ∧ entropy (levelStepTrial u n)≤entropy m ∧ _
  refine ⟨fun t => (hmu t).trans (le_levelStepTrial u n t),
    (entropy_antitone (le_levelStepTrial u n)).trans hS,?_⟩
  have hi : (∫ t, |levelStepTrial u n t-m t| ∂timeLaw) ≤
      (∫ t, |levelStepTrial u n t-u t| ∂timeLaw)+(∫ t, |u t-m t| ∂timeLaw) := by
    calc
      _ ≤ ∫ t, |levelStepTrial u n t-u t|+|u t-m t| ∂timeLaw :=
        integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
          (((trial_integrable _).sub (trial_integrable _)).abs.add
            ((trial_integrable _).sub (trial_integrable _)).abs) (fun t => abs_sub_le _ _ _)
      _ = _ := integral_add ((trial_integrable _).sub (trial_integrable _)).abs
        ((trial_integrable _).sub (trial_integrable _)).abs
  have hl := levelStepTrial_L1 u n
  change (∫ t, |levelStepTrial u n t-m t| ∂timeLaw)<ε
  linarith


 theorem expectedPressure_upper_trial
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (α : ℝ≥0) (m : Trial) (hm : entropy m≠∞) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1) ≤
      (entropy m).toReal+(α:ℝ)*controlValue P g.f m+ε := by
  let C : ℝ := (α:ℝ)*(3/2)*‖g.d1‖^2
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨k,q,hq,hq1,_,hS,hL⟩ := exists_uniform_step_trial_approx m
    (show 0<ε/(2*(C+1)) by positivity)
  let v := weightedStepTrial (fun _ : Fin (k+1) => 1/(k+1:ℝ)) q
    (uniformQuantileWeights_nonneg k) (uniformQuantileWeights_sum k)
  have hv : ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1)≤
      (entropy v).toReal+(α:ℝ)*controlValue P g.f v+ε/2 :=
    expectedPressure_upper_weightedStep k P hB g _ q (fun _ => by positivity)
      (uniformQuantileWeights_sum k) hq hq1 α (show 0<ε/2 by positivity)
  have hS' : (entropy v).toReal≤(entropy m).toReal := ENNReal.toReal_mono hm hS
  have hc := mul_le_mul_of_nonneg_left
    (controlValue_trial_sub_le P g.f v m ‖g.d1‖₊ g.lipschitz) α.coe_nonneg
  have he : C*(∫ t, |v t-m t| ∂timeLaw)≤ε/2 := by
    calc
      _ ≤ C*(ε/(2*(C+1))) := mul_le_mul_of_nonneg_left hL.le hC
      _ ≤ ε/2 := by
        rw [←mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0<2*(C+1))).mpr
        nlinarith
  filter_upwards [hv] with n hn
  dsimp only [C] at he
  change (α:ℝ)*(controlValue P g.f v-controlValue P g.f m) ≤
    (α:ℝ)*((3/2)*‖g.d1‖^2*(∫ t, |v t-m t| ∂timeLaw)) at hc
  nlinarith

 theorem expectedPressure_upper_variational
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (α : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1) ≤
      (terminalVariational P (α:ℝ) g.f).toReal+ε := by
  have hi : terminalVariational P (α:ℝ) g.f <
      (((terminalVariational P (α:ℝ) g.f).toReal+ε/2:ℝ):EReal) := by
    rw [←terminalVariational_coe_toReal P (α:ℝ) α.coe_nonneg g.f,EReal.coe_lt_coe_iff]
    simp only [EReal.toReal_coe]
    linarith
  obtain ⟨m,hm⟩ := iInf_lt_iff.mp hi
  have hS : entropy m≠∞ := by
    intro h
    simp only [h,EReal.coe_ennreal_top,EReal.coe_add_top,not_top_lt] at hm
  rw [←EReal.coe_ennreal_toReal hS,←EReal.coe_add,EReal.coe_lt_coe_iff] at hm
  filter_upwards [expectedPressure_upper_trial P hB g α m hS (show 0<ε/2 by positivity)] with n hn
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
