import Mathlib
import OAI.Probability.ThreeState.RadialDerivatives
import OAI.Probability.ThreeState.Symmetry

namespace OAI

/-! Message entropy and its integrability. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma average_message (m : Message) : avg (fun i => m i) = 1 := by
  simp [avg, Message.sum]

lemma message_last (m : Message) : m 2 = 3-m 0-m 1 := by
  have hh := average_message m
  rw [Radial.avg_expand] at hh
  linarith

lemma avg_nonneg {v : Spin → ℝ} (h : ∀ i, 0 ≤ v i) : 0 ≤ avg v :=
  div_nonneg (Finset.sum_nonneg (fun i _ => h i)) (by norm_num)

lemma avg_le_const {v : Spin → ℝ} {c : ℝ} (h : ∀ i, v i ≤ c) : avg v ≤ c := by
  rw [Radial.avg_expand]
  linarith [h 0,h 1,h 2]

lemma abs_avg_le {v : Spin → ℝ} {c : ℝ} (h : ∀ i, |v i| ≤ c) : |avg v| ≤ c := by
  apply abs_le.mpr
  constructor
  · have h0 := (abs_le.mp (h 0)).1
    have h1 := (abs_le.mp (h 1)).1
    have h2 := (abs_le.mp (h 2)).1
    rw [Radial.avg_expand]
    linarith
  · exact avg_le_const (fun i => (abs_le.mp (h i)).2)

lemma edgeMessage_bounds (lam : ℝ) (h : Admissible lam) (hl : 0 ≤ lam) (m : Message) (i : Spin) :
    1-lam ≤ edgeMessage lam h m i ∧ edgeMessage lam h m i ≤ 1+2*lam := by
  change 1-lam ≤ 1+lam*(m i-1) ∧ 1+lam*(m i-1) ≤ 1+2*lam
  constructor <;> nlinarith [Message.nonneg m i, Message.le_three m i]

lemma edgeMessage_pos (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (m : Message) (i : Spin) : 0 < edgeMessage lam h m i := by
  have hh := (edgeMessage_bounds lam h hl0 m i).1
  linarith

lemma productWeight_bounds (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (i : Spin) :
    (1-lam)^n ≤ productWeight lam h m i ∧ productWeight lam h m i ≤ (1+2*lam)^n := by
  constructor
  · calc
      (1-lam)^n = ∏ _j : Fin n, (1-lam) := by simp
      _ ≤ productWeight lam h m i := Finset.prod_le_prod₀ (fun _ _ => by linarith)
        (fun j _ => (edgeMessage_bounds lam h hl0 (m j) i).1)
  · calc
      productWeight lam h m i ≤ ∏ _j : Fin n, (1+2*lam) :=
        Finset.prod_le_prod₀ (fun j _ => Message.nonneg (edgeMessage lam h (m j)) i)
          (fun j _ => (edgeMessage_bounds lam h hl0 (m j) i).2)
      _ = (1+2*lam)^n := by simp

lemma normalizer_bounds (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) :
    (1-lam)^n ≤ normalizer lam h m ∧ normalizer lam h m ≤ (1+2*lam)^n := by
  have hh := productWeight_bounds lam h hl0 hl1 m
  change (1-lam)^n ≤ avg (productWeight lam h m) ∧ avg (productWeight lam h m) ≤ (1+2*lam)^n
  constructor
  · rw [Radial.avg_expand]
    linarith [(hh 0).1,(hh 1).1,(hh 2).1]
  · exact avg_le_const (fun i => (hh i).2)

lemma normalizer_pos (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) : 0 < normalizer lam h m :=
  lt_of_lt_of_le (pow_pos (by linarith) _) (normalizer_bounds lam h hl0 hl1 m).1

lemma combineMessage_pos (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (i : Spin) : 0 < combineMessage lam h m i := by
  have hz := normalizer_pos lam h hl0 hl1 m
  rw [combineMessage, dite_eq_right (ne_of_gt hz)]
  exact div_pos (lt_of_lt_of_le (pow_pos (by linarith) n) (productWeight_bounds lam h hl0 hl1 m i).1) hz

lemma continuous_combineMessage_positive (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) (n : ℕ) : Continuous (combineMessage lam h : (Fin n → Message) → Message) :=
  continuous_iff_continuousAt.mpr (fun m => continuousAt_combineMessage lam h m
    (ne_of_gt (normalizer_pos lam h hl0 hl1 m)))

lemma positive_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q) :
    ∀ᵐ m ∂(Q : Measure Message), ∀ i : Spin, 0 < m i := by
  apply ae_fixedpoint_of_output offspring lam h Q hQ
  · simpa only [Set.ofPred_forall, Function.comp_def] using MeasurableSet.iInter (fun i : Spin =>
      measurableSet_lt (f := fun _ : Message => (0:ℝ)) measurable_const
        ((continuous_apply i).comp continuous_subtype_val).measurable)
  · intro n m i
    exact combineMessage_pos lam h hl0 hl1 m i

noncomputable def edgeLogBound (lam : ℝ) : ℝ := |Real.log (1-lam)|+|Real.log (1+2*lam)|

lemma edgeLogBound_nonneg (lam : ℝ) : 0 ≤ edgeLogBound lam := add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma abs_log_of_bounds (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (n : ℕ) (a : ℝ)
    (ha : (1-lam)^n ≤ a) (hb : a ≤ (1+2*lam)^n) : |Real.log a| ≤ n*edgeLogBound lam := by
  have ha0 : 0 < (1-lam)^n := pow_pos (by linarith) _
  have hap : 0 < a := lt_of_lt_of_le ha0 ha
  have hlo := Real.log_le_log ha0 ha
  have hhi : Real.log a ≤ Real.log ((1+2*lam)^n) :=
    (Real.log_le_log_iff hap (pow_pos (by linarith [hl0]) n)).mpr hb
  rw [Real.log_pow] at hlo hhi
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 := neg_abs_le (Real.log (1-lam))
  have ha2 := le_abs_self (Real.log (1+2*lam))
  dsimp [edgeLogBound]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hn (abs_nonneg (Real.log (1+2*lam)))]
  · nlinarith [mul_nonneg hn (abs_nonneg (Real.log (1-lam)))]

lemma log_combineMessage (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (i : Spin) :
    Real.log (combineMessage lam h m i) =
      (∑ j, Real.log (edgeMessage lam h (m j) i))-Real.log (normalizer lam h m) := by
  have hz := normalizer_pos lam h hl0 hl1 m
  have hw : productWeight lam h m i ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (pow_pos (by linarith) n) (productWeight_bounds lam h hl0 hl1 m i).1)
  rw [combineMessage, dite_eq_right (ne_of_gt hz), Real.log_div hw (ne_of_gt hz)]
  rw [productWeight, Real.log_prod (fun j _ => ne_of_gt (edgeMessage_pos lam h hl0 hl1 (m j) i))]

lemma log_combineMessage_bound (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (i : Spin) :
    |Real.log (combineMessage lam h m i)| ≤ 2*n*edgeLogBound lam := by
  have hz := normalizer_pos lam h hl0 hl1 m
  have hw := productWeight_bounds lam h hl0 hl1 m i
  have hn := normalizer_bounds lam h hl0 hl1 m
  have hw0 : productWeight lam h m i ≠ 0 := ne_of_gt (lt_of_lt_of_le (pow_pos (by linarith) n) hw.1)
  rw [combineMessage, dite_eq_right (ne_of_gt hz), Real.log_div hw0 (ne_of_gt hz)]
  calc
    |Real.log (productWeight lam h m i)-Real.log (normalizer lam h m)| ≤
      |Real.log (productWeight lam h m i)|+|Real.log (normalizer lam h m)| := abs_sub _ _
    _ ≤ n*edgeLogBound lam+n*edgeLogBound lam := add_le_add
      (abs_log_of_bounds lam hl0 hl1 n _ hw.1 hw.2) (abs_log_of_bounds lam hl0 hl1 n _ hn.1 hn.2)
    _ = _ := by ring

noncomputable def mLog (m : Message) (i : Spin) : ℝ := Real.log (m i)
noncomputable def mCenteredLog (m : Message) (i : Spin) : ℝ := mLog m i-avg (mLog m)
noncomputable def entropyI (m : Message) : ℝ := avg (fun i => m i*mLog m i)
noncomputable def entropyJ (m : Message) : ℝ := avg (fun i => (m i-1)*mLog m i)/2
noncomputable def entropyB (m : Message) : ℝ := avg (fun i => m i*(mCenteredLog m i)^2)/2
noncomputable def entropyF (m : Message) : ℝ := 3*entropyI m-2*entropyJ m+(4/5:ℝ)*entropyB m

lemma measurable_mLog (i : Spin) : Measurable (fun m : Message => mLog m i) :=
  Real.measurable_log.comp ((continuous_apply i).comp continuous_subtype_val).measurable
lemma measurable_avg (f : Message → Spin → ℝ) (hf : ∀ i, Measurable (fun m => f m i)) :
    Measurable (fun m => avg (f m)) := by
  simp only [Radial.avg_expand]
  exact (((hf 0).add (hf 1)).add (hf 2)).div_const 3
lemma measurable_mCenteredLog (i : Spin) : Measurable (fun m : Message => mCenteredLog m i) :=
  (measurable_mLog i).sub (measurable_avg mLog measurable_mLog)
lemma measurable_entropyI : Measurable entropyI :=
  measurable_avg _ (fun i => ((continuous_apply i).comp continuous_subtype_val).measurable.mul (measurable_mLog i))
lemma measurable_entropyJ : Measurable entropyJ :=
  (measurable_avg _ (fun i => (((continuous_apply i).comp continuous_subtype_val).measurable.sub_const 1).mul (measurable_mLog i))).div_const 2
lemma measurable_entropyB : Measurable entropyB :=
  (measurable_avg _ (fun i => ((continuous_apply i).comp continuous_subtype_val).measurable.mul ((measurable_mCenteredLog i).pow_const 2))).div_const 2
lemma measurable_entropyF : Measurable entropyF := by
  exact ((measurable_entropyI.const_mul 3).sub (measurable_entropyJ.const_mul 2)).add
    (measurable_entropyB.const_mul (4/5:ℝ))

lemma centeredLog_combine (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (i : Spin) :
    mCenteredLog (combineMessage lam h m) i = ∑ j, mCenteredLog (edgeMessage lam h (m j)) i := by
  simp only [mCenteredLog, mLog, Radial.avg_expand, log_combineMessage lam h hl0 hl1,
    Finset.sum_sub_distrib, add_div, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

lemma centeredLog_J (m : Message) : avg (fun i => m i*mCenteredLog m i) = 2*entropyJ m := by
  simp only [mCenteredLog, entropyJ, mLog, Radial.avg_expand, message_last m]
  ring

lemma entropyF_radial (m : Message) : entropyF m = Radial.sourceF (fun i => m i) := by
  simp only [entropyF, entropyI, entropyJ, entropyB, mCenteredLog, mLog, Radial.sourceF,
    Radial.avg_expand]
  ring

lemma centeredLog_bound (m : Message) (C : ℝ) (hc : ∀ i, |mLog m i| ≤ C) (i : Spin) :
    |mCenteredLog m i| ≤ 2*C := by
  calc
    |mCenteredLog m i| ≤ |mLog m i|+|avg (mLog m)| := abs_sub _ _
    _ ≤ C+C := add_le_add (hc i) (abs_avg_le hc)
    _ = _ := by ring

lemma entropyI_bound (m : Message) (C : ℝ) (hc : ∀ i, |mLog m i| ≤ C) : |entropyI m| ≤ 3*C := by
  apply abs_avg_le
  intro i
  rw [abs_mul, abs_of_nonneg (Message.nonneg m i)]
  exact mul_le_mul (Message.le_three m i) (hc i) (abs_nonneg _) (by norm_num)

lemma entropyJ_bound (m : Message) (C : ℝ) (hc : ∀ i, |mLog m i| ≤ C) : |entropyJ m| ≤ C := by
  have hv (i : Spin) : |m i-1| ≤ 2 := abs_le.mpr ⟨by linarith [Message.nonneg m i], by linarith [Message.le_three m i]⟩
  have ha : |avg (fun i => (m i-1)*mLog m i)| ≤ 2*C := by
    apply abs_avg_le
    intro i
    rw [abs_mul]
    exact mul_le_mul (hv i) (hc i) (abs_nonneg _) (by norm_num)
  dsimp only [entropyJ]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

lemma entropyB_nonneg (m : Message) : 0 ≤ entropyB m :=
  div_nonneg (avg_nonneg (fun i => mul_nonneg (Message.nonneg m i) (sq_nonneg _))) (by norm_num)

lemma entropyB_bound (m : Message) (C : ℝ) (hc : ∀ i, |mLog m i| ≤ C) : |entropyB m| ≤ 6*C^2 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hc 0)
  have hu (i : Spin) : (mCenteredLog m i)^2 ≤ (2*C)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (mCenteredLog m i)) (by positivity : 0 ≤ 2*C)).mpr (centeredLog_bound m C hc i)
    simpa only [sq_abs] using hh
  have ha : avg (fun i => m i*(mCenteredLog m i)^2) ≤ 12*C^2 := by
    apply avg_le_const
    intro i
    have hh := mul_le_mul (Message.le_three m i) (hu i) (sq_nonneg _) (by norm_num : (0:ℝ)≤3)
    nlinarith
  rw [abs_of_nonneg (entropyB_nonneg m)]
  dsimp only [entropyB]
  linarith

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma continuous_avg {α : Type*} [TopologicalSpace α] (f : α → Spin → ℝ)
    (hf : ∀ i, Continuous (fun m => f m i)) : Continuous (fun m => avg (f m)) := by
  simp only [Radial.avg_expand]
  exact (((hf 0).add (hf 1)).add (hf 2)).div_const 3

lemma continuous_mLog_edge (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (i : Spin) :
    Continuous (fun m => mLog (edgeMessage lam h m) i) :=
  (((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)).log
    (fun m => ne_of_gt (edgeMessage_pos lam h hl0 hl1 m i))

lemma continuous_mCenteredLog_edge (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (i : Spin) :
    Continuous (fun m => mCenteredLog (edgeMessage lam h m) i) :=
  (continuous_mLog_edge lam h hl0 hl1 i).sub
    (continuous_avg _ (continuous_mLog_edge lam h hl0 hl1))

lemma continuous_entropyI_edge (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    Continuous (fun m => entropyI (edgeMessage lam h m)) :=
  continuous_avg _ (fun i =>
    (((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)).mul
      (continuous_mLog_edge lam h hl0 hl1 i))

lemma continuous_entropyJ_edge (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    Continuous (fun m => entropyJ (edgeMessage lam h m)) :=
  (continuous_avg _ (fun i =>
    ((((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)).sub continuous_const).mul
      (continuous_mLog_edge lam h hl0 hl1 i))).div_const 2

lemma continuous_entropyB_edge (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    Continuous (fun m => entropyB (edgeMessage lam h m)) :=
  (continuous_avg _ (fun i =>
    (((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h)).mul
      ((continuous_mCenteredLog_edge lam h hl0 hl1 i).pow 2))).div_const 2

lemma integrable_mLog_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) (i : Spin) :
    Integrable (fun m => mLog m i) (Q : Measure Message) := by
  apply integrable_fixedpoint_of_growth offspring lam h Q hQ _ (measurable_mLog i)
    (fun n => (n:ℝ)*(2*edgeLogBound lam)) (hD.mul_const _)
  intro n m
  have hh := log_combineMessage_bound lam h hl0 hl1 m i
  dsimp only [mLog]
  nlinarith

lemma integrable_entropyI_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) :
    Integrable entropyI (Q : Measure Message) := by
  apply integrable_fixedpoint_of_growth offspring lam h Q hQ _ measurable_entropyI
    (fun n => (n:ℝ)*(6*edgeLogBound lam)) (hD.mul_const _)
  intro n m
  have hh := entropyI_bound (combineMessage lam h m) (2*n*edgeLogBound lam)
    (log_combineMessage_bound lam h hl0 hl1 m)
  nlinarith

lemma integrable_entropyJ_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) :
    Integrable entropyJ (Q : Measure Message) := by
  apply integrable_fixedpoint_of_growth offspring lam h Q hQ _ measurable_entropyJ
    (fun n => (n:ℝ)*(2*edgeLogBound lam)) (hD.mul_const _)
  intro n m
  have hh := entropyJ_bound (combineMessage lam h m) (2*n*edgeLogBound lam)
    (log_combineMessage_bound lam h hl0 hl1 m)
  nlinarith

lemma integrable_entropyB_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD2 : HasMean offspring (fun n : ℕ => (n:ℝ)^2)) :
    Integrable entropyB (Q : Measure Message) := by
  apply integrable_fixedpoint_of_growth offspring lam h Q hQ _ measurable_entropyB
    (fun n => (n:ℝ)^2*(24*(edgeLogBound lam)^2)) (hD2.mul_const _)
  intro n m
  have hh := entropyB_bound (combineMessage lam h m) (2*n*edgeLogBound lam)
    (log_combineMessage_bound lam h hl0 hl1 m)
  nlinarith

lemma integrable_entropyF_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD2 : HasMean offspring (fun n : ℕ => (n:ℝ)^2)) :
    Integrable entropyF (Q : Measure Message) := by
  have hD := hasMean_of_square hD2
  exact (((integrable_entropyI_fixedpoint offspring lam h hl0 hl1 Q hQ hD).const_mul 3).sub
    ((integrable_entropyJ_fixedpoint offspring lam h hl0 hl1 Q hQ hD).const_mul 2)).add
      ((integrable_entropyB_fixedpoint offspring lam h hl0 hl1 Q hQ hD2).const_mul (4/5:ℝ))

end ThreeState

end OAI
