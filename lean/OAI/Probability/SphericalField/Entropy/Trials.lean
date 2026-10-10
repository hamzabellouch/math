import Mathlib
import OAI.Probability.SphericalField.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial

lemma trial_integrable (m : Trial) : Integrable m timeLaw := by
  apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (m.nonneg t)]
    exact m.le_one t

lemma tailIntegral_mono {m n : Trial} (h : ∀ t, m t ≤ n t) (t : Time) :
    tailIntegral m t ≤ tailIntegral n t :=
  integral_mono (trial_integrable m).integrableOn (trial_integrable n).integrableOn h

lemma entropy_antitone {m n : Trial} (h : ∀ t, m t ≤ n t) : entropy n ≤ entropy m := by
  apply ENNReal.div_le_div_right
  apply lintegral_mono
  intro t
  exact tsub_le_tsub_right (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (tailIntegral_mono h t))) _

def upperRoundedTrial (m : Trial) (n : ℕ) : Trial where
  toFun := fun t => (⌈((n+1 : ℕ) : ℝ)*m t⌉₊ : ℝ) / (n+1 : ℕ)
  monotone := by
    intro s t hst
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left (m.monotone hst) (by positivity))
  measurable :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (Nat.measurable_ceil.comp (measurable_const.mul m.measurable))).div_const _
  nonneg := by intro t; positivity
  le_one := by
    intro t
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Nat.ceil_le.mpr (show (((n+1 : ℕ) : ℝ)*m t) ≤ ((n+1 : ℕ) : ℝ) by
      nlinarith [m.le_one t]))

lemma le_upperRoundedTrial (m : Trial) (n : ℕ) (t : Time) : m t ≤ upperRoundedTrial m n t := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
  simpa only [mul_comm] using (Nat.le_ceil (((n+1 : ℕ) : ℝ)*m t))

lemma upperRoundedTrial_sub_le (m : Trial) (n : ℕ) (t : Time) :
    upperRoundedTrial m n t - m t ≤ 1/((n+1 : ℕ) : ℝ) := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ)*m t from mul_nonneg (by positivity) (m.nonneg t))
  change (⌈((n+1 : ℕ) : ℝ)*m t⌉₊ : ℝ) / (n+1 : ℕ) - m t ≤ _
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
  have hn : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma upperRoundedTrial_finite_range (m : Trial) (n : ℕ) :
    (Set.range (upperRoundedTrial m n)).Finite := by
  apply (Set.finite_Iic (n+1)).image (fun k : ℕ => (k : ℝ)/((n+1 : ℕ) : ℝ)) |>.subset
  rintro _ ⟨t,rfl⟩
  refine ⟨⌈((n+1 : ℕ) : ℝ)*m t⌉₊, ?_, rfl⟩
  exact Nat.ceil_le.mpr (by nlinarith [m.le_one t])

def terminalTrial (m : Trial) (r : Time) : Trial where
  toFun := fun t => if r ≤ t then 1 else m t
  monotone := by
    intro s t hst
    by_cases hs : r ≤ s
    · simp only [ite_eq_left hs,ite_eq_left (hs.trans hst)]
      exact le_rfl
    · by_cases ht : r ≤ t
      · simpa only [ite_eq_right hs,ite_eq_left ht] using m.le_one s
      · simpa only [ite_eq_right hs,ite_eq_right ht] using m.monotone hst
  measurable := Measurable.ite measurableSet_Ici measurable_const m.measurable
  nonneg := by intro t; split_ifs; norm_num; exact m.nonneg t
  le_one := by intro t; split_ifs; exact le_rfl; exact m.le_one t

lemma le_terminalTrial (m : Trial) (r t : Time) : m t ≤ terminalTrial m r t := by
  change m t ≤ if r ≤ t then 1 else m t
  split_ifs; exact m.le_one t; exact le_rfl

lemma terminalTrial_finite_range (m : Trial) (r : Time) (h : (Set.range m).Finite) :
    (Set.range (terminalTrial m r)).Finite := by
  apply (h.insert 1).subset
  rintro _ ⟨t,rfl⟩
  change (if r ≤ t then 1 else m t) ∈ _
  split_ifs
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_range_self t)

lemma terminalTrial_tail (m : Trial) {r t : Time} (hrt : r ≤ t) :
    tailIntegral (terminalTrial m r) t = 1 - (t : ℝ) := by
  have he : (fun s : Time => terminalTrial m r s) =ᵐ[timeLaw.restrict (Ici t)] (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    simp only [terminalTrial, ite_eq_left (hrt.trans hs)]
  rw [tailIntegral,integral_congr_ae he]
  simp [Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr t.property.2]

lemma tailIntegral_antitone (m : Trial) : Antitone (tailIntegral m) := by
  intro s t hst
  apply setIntegral_mono_set (trial_integrable m).integrableOn
    (Eventually.of_forall fun x => m.nonneg x)
  exact Filter.Eventually.of_forall (fun x hx => hst.trans hx)

lemma terminalTrial_entropy_finite (m : Trial) {r : Time} (hr : (r : ℝ) < 1) :
    entropy (terminalTrial m r) < ∞ := by
  have hbound : (∫⁻ t, (ENNReal.ofReal (tailIntegral (terminalTrial m r) t))⁻¹ -
      (ENNReal.ofReal (1-(t : ℝ)))⁻¹ ∂timeLaw) ≤ (ENNReal.ofReal (1-(r : ℝ)))⁻¹ := by
    calc
      _ ≤ ∫⁻ _t : Time, (ENNReal.ofReal (1-(r : ℝ)))⁻¹ ∂timeLaw := by
        apply lintegral_mono
        intro t
        dsimp only
        by_cases ht : r ≤ t
        · rw [terminalTrial_tail m ht,tsub_self]
          exact bot_le
        · have htr : t ≤ r := le_of_not_ge ht
          have hd := tailIntegral_antitone (terminalTrial m r) htr
          rw [terminalTrial_tail m le_rfl] at hd
          exact (tsub_le_self).trans (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hd))
      _ = _ := by simp
  unfold entropy
  apply ENNReal.div_lt_top _ (by norm_num)
  exact (hbound.trans_lt (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr)))).ne

lemma terminalTrial_L1_le (m : Trial) (r : Time) :
    (∫ t, |terminalTrial m r t - m t| ∂timeLaw) ≤ 1-(r : ℝ) := by
  calc
    _ ≤ ∫ t, (Ici r).indicator (fun _ => (1 : ℝ)) t ∂timeLaw := by
      apply integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
        ((integrable_const (1 : ℝ)).indicator measurableSet_Ici)
      intro t
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_terminalTrial m r t))]
      by_cases ht : r ≤ t
      · simp only [terminalTrial,ite_eq_left ht,Set.indicator_of_mem (show t ∈ Ici r from ht)]
        linarith [m.nonneg t]
      · simp only [terminalTrial,ite_eq_right ht,Set.indicator_of_notMem (show t ∉ Ici r from ht),sub_self]
        exact le_rfl
    _ = 1-(r : ℝ) := by
      rw [integral_indicator measurableSet_Ici]
      simp [Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr r.property.2]

lemma upperRoundedTrial_L1_le (m : Trial) (n : ℕ) :
    (∫ t, |upperRoundedTrial m n t - m t| ∂timeLaw) ≤ 1/((n+1 : ℕ) : ℝ) := by
  calc
    _ ≤ ∫ _t : Time, (1 : ℝ)/((n+1 : ℕ) : ℝ) ∂timeLaw := by
      apply integral_mono ((trial_integrable _).sub (trial_integrable _)).abs (integrable_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_upperRoundedTrial m n t))]
      exact upperRoundedTrial_sub_le m n t
    _ = _ := by simp

lemma exists_finite_terminal_trial_approx (m : Trial) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Trial, (Set.range q).Finite ∧ (∃ r : Time, (r : ℝ) < 1 ∧ ∀ t, r ≤ t → q t = 1) ∧
      (∀ t, m t ≤ q t) ∧ entropy q ≤ entropy m ∧ entropy q < ∞ ∧
      (∫ t, |q t-m t| ∂timeLaw) < ε := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (half_pos hε)
  let r : Time := ⟨1-min (ε/2) (1/2),by constructor <;> linarith [min_le_left (ε/2) (1/2),min_le_right (ε/2) (1/2),lt_min (half_pos hε) (by norm_num : (0:ℝ)<1/2)]⟩
  have hr : (r : ℝ) < 1 := by dsimp [r]; exact sub_lt_self _ (lt_min (half_pos hε) (by norm_num))
  let q := terminalTrial (upperRoundedTrial m n) r
  have hmq (t : Time) : m t ≤ q t := (le_upperRoundedTrial m n t).trans (le_terminalTrial _ r t)
  refine ⟨q,terminalTrial_finite_range _ r (upperRoundedTrial_finite_range m n),
    ⟨r,hr,fun t ht => by simp [q,terminalTrial,ht]⟩,hmq,entropy_antitone hmq,
    terminalTrial_entropy_finite _ hr,?_⟩
  calc
    _ ≤ (∫ t, |q t-upperRoundedTrial m n t| + |upperRoundedTrial m n t-m t| ∂timeLaw) :=
      integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
        (((trial_integrable _).sub (trial_integrable _)).abs.add
          ((trial_integrable _).sub (trial_integrable _)).abs) (fun t => abs_sub_le _ _ _)
    _ = (∫ t, |q t-upperRoundedTrial m n t| ∂timeLaw) +
        ∫ t, |upperRoundedTrial m n t-m t| ∂timeLaw :=
      integral_add ((trial_integrable _).sub (trial_integrable _)).abs ((trial_integrable _).sub (trial_integrable _)).abs
    _ ≤ 1-(r : ℝ)+1/((n+1 : ℕ) : ℝ) := add_le_add (terminalTrial_L1_le _ r) (upperRoundedTrial_L1_le m n)
    _ < ε := by
      have hn' : 1/((n+1 : ℕ) : ℝ) < ε/2 := by simpa only [Nat.cast_add,Nat.cast_one] using hn
      dsimp [r]
      linarith [min_le_left (ε/2) (1/2)]

end SphericalPerceptron
end
end
end

end OAI
