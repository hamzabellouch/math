import Mathlib
import OAI.Probability.Perceptron.Variational.StepDual
import OAI.Probability.Perceptron.Variational.Entropy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def stepTailSum {k : ℕ} (v : Fin k → ℝ) (i : Fin (k+1)) : ℝ :=
  ∑ j : Fin k, if i ≤ j.castSucc then v j else 0

lemma stepTailSum_zero {k : ℕ} (v : Fin k → ℝ) : stepTailSum v 0=∑ j, v j := by
  simp only [stepTailSum,Fin.zero_le,ite_true]

lemma stepTailSum_last {k : ℕ} (v : Fin k → ℝ) : stepTailSum v (Fin.last k)=0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : ¬Fin.last k ≤ j.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]; omega
  exact ite_eq_right hj

lemma stepTailSum_difference {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    stepTailSum v i.castSucc-stepTailSum v i.succ=v i := by
  classical
  unfold stepTailSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin k, if j=i then v j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j=i
      · subst j
        have hi : ¬i.succ ≤ i.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]; omega
        simp only [ite_eq_left le_rfl,ite_eq_right hi,sub_zero,ite_true]
      · have he : (i.castSucc ≤ j.castSucc) ↔ (i.succ ≤ j.castSucc) := by
          simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]
          have hv : i.val ≠ j.val := by intro hij; exact hji (Fin.ext hij.symm)
          omega
        simp only [he,sub_self,ite_eq_right hji]
    _ = _ := by simp

lemma stepTailSum_nonneg {k : ℕ} (v : Fin k → ℝ) (hv : ∀ j, 0 ≤ v j) (i : Fin (k+1)) :
    0 ≤ stepTailSum v i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> first | exact hv j | rfl

lemma stepTailSum_le_zero {k : ℕ} (v : Fin k → ℝ) (hv : ∀ j, 0 ≤ v j) (i : Fin (k+1)) :
    stepTailSum v i ≤ stepTailSum v 0 := by
  rw [stepTailSum_zero]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> first | rfl | exact hv j

def finitePrecisionShift {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  stepTailSum (fun i => 2*z i*(h i.succ-h i.castSucc))

def finitePrecisionTail {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (b : ℝ) (i : Fin (k+1)) : ℝ := (b-finitePrecisionShift z h i)⁻¹

def finiteOverlapIncrement {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (b : ℝ) (i : Fin k) : ℝ :=
  2*(h i.succ-h i.castSucc)*finitePrecisionTail z h b i.castSucc*finitePrecisionTail z h b i.succ

def finiteStationarityMass {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) (b : ℝ) : ℝ :=
  2*h 0*(finitePrecisionTail z h b 0)^2+(∑ i, finiteOverlapIncrement z h b i)+
    finitePrecisionTail z h b (Fin.last k)

lemma finitePrecisionShift_le_root {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) (i : Fin (k+1)) :
    finitePrecisionShift z h i ≤ finitePrecisionShift z h 0 :=
  stepTailSum_le_zero _ (fun j => mul_nonneg (mul_nonneg (by norm_num) (hz j))
    (sub_nonneg.mpr (hh (Fin.castSucc_le_succ j)))) i

lemma finitePrecisionTail_pos {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin (k+1)) : 0 < finitePrecisionTail z h b i :=
  inv_pos.mpr (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i).trans_lt hb))

lemma finitePrecisionTail_gap {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin k) : finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ =
      z i*finiteOverlapIncrement z h b i := by
  have h1 : b-finitePrecisionShift z h i.castSucc ≠ 0 :=
    (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i.castSucc).trans_lt hb)).ne'
  have h2 : b-finitePrecisionShift z h i.succ ≠ 0 :=
    (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i.succ).trans_lt hb)).ne'
  have he := stepTailSum_difference (fun j => 2*z j*(h j.succ-h j.castSucc)) i
  change finitePrecisionShift z h i.castSucc-finitePrecisionShift z h i.succ =
    2*z i*(h i.succ-h i.castSucc) at he
  unfold finiteOverlapIncrement finitePrecisionTail
  field_simp [h1,h2]
  linear_combination he

lemma finiteOverlapIncrement_nonneg {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin k) : 0 ≤ finiteOverlapIncrement z h b i := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i))))
    (finitePrecisionTail_pos z h hz hh hb i.castSucc).le) (finitePrecisionTail_pos z h hz hh hb i.succ).le

lemma finiteStationarityMass_ge_root {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hh : Monotone h) (hh0 : 0 ≤ h 0)
    {b : ℝ} (hb : finitePrecisionShift z h 0 < b) :
    finitePrecisionTail z h b 0 ≤ finiteStationarityMass z h b := by
  have hg (i : Fin k) : finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ ≤
      finiteOverlapIncrement z h b i := by
    rw [finitePrecisionTail_gap z h hz0 hh hb i]
    exact mul_le_of_le_one_left (finiteOverlapIncrement_nonneg z h hz0 hh hb i) (hz1 i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hg i)
  have ht := finite_sum_successive_differences k (finitePrecisionTail z h b)
  have he : (∑ i : Fin k, (finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ)) =
      finitePrecisionTail z h b 0-finitePrecisionTail z h b (Fin.last k) := by
    rw [Finset.sum_sub_distrib] at ht ⊢
    linarith
  rw [he] at hs
  have hn : 0 ≤ 2*h 0*(finitePrecisionTail z h b 0)^2 := by positivity
  unfold finiteStationarityMass
  linarith

lemma finiteStationarityMass_continuousOn {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) :
    ContinuousOn (finiteStationarityMass z h) (Ici (finitePrecisionShift z h 0+1)) := by
  have hc (i : Fin (k+1)) : ContinuousOn (fun b => finitePrecisionTail z h b i)
      (Ici (finitePrecisionShift z h 0+1)) := by
    apply (continuous_id.sub continuous_const).continuousOn.inv₀
    intro b hb
    have hi := finitePrecisionShift_le_root z h hz hh i
    change finitePrecisionShift z h 0+1 ≤ b at hb
    change b-finitePrecisionShift z h i ≠ 0
    exact (sub_pos.mpr (by linarith)).ne'
  exact ((continuousOn_const.mul (hc 0 |>.pow 2)).add
    (continuousOn_finsetSum Finset.univ (fun i _ =>
      (continuousOn_const.mul (hc i.castSucc)).mul (hc i.succ)))).add (hc (Fin.last k))

lemma finiteStationarityMass_tendsto {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) :
    Tendsto (finiteStationarityMass z h) atTop (𝓝 0) := by
  have ht (i : Fin (k+1)) : Tendsto (fun b => finitePrecisionTail z h b i) atTop (𝓝 0) := by
    simpa only [finitePrecisionTail,sub_eq_add_neg,Function.comp_def,id_eq] using
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-finitePrecisionShift z h i) tendsto_id))
  have hi (i : Fin k) : Tendsto (fun b => finiteOverlapIncrement z h b i) atTop (𝓝 0) := by
    simpa only [finiteOverlapIncrement,mul_zero] using ((ht i.castSucc).const_mul (2*(h i.succ-h i.castSucc))).mul (ht i.succ)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hf := (((ht 0).pow 2).const_mul (2*h 0)).add hs |>.add (ht (Fin.last k))
  change Tendsto (fun b => 2*h 0*(finitePrecisionTail z h b 0)^2+
    (∑ i, finiteOverlapIncrement z h b i)+finitePrecisionTail z h b (Fin.last k)) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,Finset.sum_const_zero,zero_add] using hf

theorem exists_finite_normalizing_precision {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ b : ℝ, finitePrecisionShift z h 0 < b ∧ finiteStationarityMass z h b=1 := by
  let a := finitePrecisionShift z h 0+1
  have ha : finitePrecisionShift z h 0 < a := by dsimp only [a]; linarith
  have hstart : 1 ≤ finiteStationarityMass z h a := by
    have hs := finiteStationarityMass_ge_root z h hz0 hz1 hh hh0 ha
    simpa only [finitePrecisionTail,a,add_sub_cancel_left,inv_one] using hs
  have hev := (finiteStationarityMass_tendsto z h).eventually_lt_const (by norm_num : (0:ℝ)<1)
  obtain ⟨b,hb,hend⟩ := ((eventually_ge_atTop a).and hev).exists
  have hc : ContinuousOn (finiteStationarityMass z h) (Icc a b) :=
    (finiteStationarityMass_continuousOn z h hz0 hh).mono Icc_subset_Ici_self
  obtain ⟨c,hc,he⟩ := intermediate_value_Icc' hb hc ⟨hend.le,hstart⟩
  exact ⟨c,ha.trans_le hc.1,he⟩

theorem exists_finite_stationary_quantile {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
      ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i) := by
  let z := stepCumulative w
  have hz0 : ∀ i, 0 < z i := stepCumulative_pos w hw
  have hz1 : ∀ i, z i < 1 := stepCumulative_lt_one w hw hw1
  obtain ⟨b,hb,hb1⟩ := exists_finite_normalizing_precision z h
    (fun i => (hz0 i).le) (fun i => (hz1 i).le) hh hh0
  let D := finitePrecisionTail z h b
  let v := finiteOverlapIncrement z h b
  let Q : Fin (k+1) → ℝ := fun i => 2*h 0*(D 0)^2+(∑ j, v j)-stepTailSum v i
  have hD (i : Fin (k+1)) : 0 < D i := finitePrecisionTail_pos z h (fun i => (hz0 i).le) hh hb i
  have hv (i : Fin k) : 0 ≤ v i := finiteOverlapIncrement_nonneg z h (fun i => (hz0 i).le) hh hb i
  have hQ0 : Q 0=2*h 0*(D 0)^2 := by simp only [Q,stepTailSum_zero]; ring
  have hQlast : Q (Fin.last k)=2*h 0*(D 0)^2+∑ j, v j := by simp only [Q,stepTailSum_last,sub_zero]
  have hQinc (i : Fin k) : Q i.succ-Q i.castSucc=v i := by
    have he := stepTailSum_difference v i
    dsimp only [Q]
    linarith
  have hQmono : Monotone Q := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have he := hQinc i
    linarith [hv i]
  have hQ0pos : 0 ≤ Q 0 := by rw [hQ0]; positivity
  have hnorm : Q (Fin.last k)+D (Fin.last k)=1 := by
    rw [hQlast]
    exact hb1
  have hQ1 : Q (Fin.last k) < 1 := by linarith [hD (Fin.last k)]
  have hgap (i : Fin k) : D i.castSucc-D i.succ=z i*(Q i.succ-Q i.castSucc) := by
    rw [hQinc]
    exact finitePrecisionTail_gap z h (fun i => (hz0 i).le) hh hb i
  let T : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hTgap (i : Fin k) : T i.castSucc-T i.succ=z i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hQmono i (t := Q i.succ) ⟨hQmono (Fin.castSucc_le_succ i),le_rfl⟩
    change T i.succ=T i.castSucc-z i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hTlast : T (Fin.last k)=D (Fin.last k) := by
    have he := weightedStepTail_of_le w Q hw1 (fun i => hQmono (Fin.le_last i))
    change T (Fin.last k)=1-Q (Fin.last k) at he
    linarith
  have hconst (i : Fin (k+1)) : T i-D i=T 0-D 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => linarith [hTgap i,hgap i]
  have hTD (i : Fin (k+1)) : T i=D i := by
    have he := hconst (Fin.last k)
    rw [hTlast] at he
    linarith [hconst i]
  have hroot : 2*h 0=Q 0/(T 0)^2 := by
    rw [hTD,hQ0]
    have hn : D 0 ≠ 0 := (hD 0).ne'
    field_simp [hn]
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=(Q i.succ-Q i.castSucc)/(T i.castSucc*T i.succ) := by
    rw [hQinc,hTD,hTD]
    change 2*(h i.succ-h i.castSucc)=
      (2*(h i.succ-h i.castSucc)*D i.castSucc*D i.succ)/(D i.castSucc*D i.succ)
    have hn : D i.castSucc ≠ 0 := (hD i.castSucc).ne'
    have hn' : D i.succ ≠ 0 := (hD i.succ).ne'
    field_simp [hn,hn']
  have hstat (i : Fin (k+1)) : 2*h i=weightedStepA w Q (Q i) := by
    induction i using Fin.induction with
    | zero => rw [weightedStepA_root w Q hQmono hQ0pos]; exact hroot
    | succ i ih =>
      have he := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hQmono hQ0pos hQ1 i (hz0 i)
      change weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc)=
        (Q i.succ-Q i.castSucc)/(T i.castSucc*T i.succ) at he
      linarith [hinc i]
  let q : Fin (k+1) → Time := fun i => ⟨Q i,⟨hQ0pos.trans (hQmono (Fin.zero_le i)),
    ((hQmono (Fin.le_last i)).trans_lt hQ1).le⟩⟩
  exact ⟨q,(fun i j hij => hQmono hij),hQ1,hstat⟩

def finiteSphericalDualObjective {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (q : Fin (k+1) → Time) : ℝ :=
  (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ)

def finiteSphericalDualValues {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) : Set ℝ :=
  finiteSphericalDualObjective w h hw hw1 ''
    {q : Fin (k+1) → Time | Monotone q ∧ (q (Fin.last k):ℝ) < 1}

theorem finiteSphericalFieldValue_pointwise_dual {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
      IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
        (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) ∧
      Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
        (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1))) := by
  obtain ⟨q,hq,hq1,hs⟩ := exists_finite_stationary_quantile w h hw hw1 hh hh0
  have hleast : IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
      (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) := by
    refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
    rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
    exact stationary_finite_entropy_minimizes w h q p (fun i => (hw i).le) hw1 hq hp hq1 hp1 hs
  refine ⟨q,hq,hq1,hleast,?_⟩
  rw [hleast.csInf_eq]
  exact finiteSphericalFieldValue_stationary w h q hw hw1 hq hq1 hs

end SphericalPerceptronFreeEnergy
end

end OAI
