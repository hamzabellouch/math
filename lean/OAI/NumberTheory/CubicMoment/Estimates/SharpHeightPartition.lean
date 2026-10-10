import OAI.NumberTheory.CubicMoment.Estimates.SharpHeightIntegral
import OAI.NumberTheory.CubicMoment.Estimates.DyadicWeightIntegral

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def heightPartitionBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 4/3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma heightPartitionBump_one {t : ℝ} (ht : |t| ≤ 1) :
    heightPartitionBump t = 1 := by
  apply heightPartitionBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, heightPartitionBump] using ht

lemma heightPartitionBump_zero {t : ℝ} (ht : 4/3 ≤ |t|) :
    heightPartitionBump t = 0 := by
  apply heightPartitionBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, heightPartitionBump] using ht

def heightWindow (T t : ℝ) : ℂ :=
  ((heightPartitionBump (t/((3/2)*T)) - heightPartitionBump (t/T) : ℝ) : ℂ)

lemma heightWindow_smooth (T : ℝ) : ContDiff ℝ ∞ (heightWindow T) := by
  exact Complex.ofRealCLM.contDiff.comp
    ((heightPartitionBump.contDiff.comp (contDiff_id.div_const _)).sub
      (heightPartitionBump.contDiff.comp (contDiff_id.div_const _)))

lemma heightWindow_norm_le (T t : ℝ) : ‖heightWindow T t‖ ≤ 1 := by
  rw [heightWindow, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [heightPartitionBump.nonneg (x := t/((3/2)*T)),
    heightPartitionBump.le_one (x := t/((3/2)*T)),
    heightPartitionBump.nonneg (x := t/T), heightPartitionBump.le_one (x := t/T)]

lemma heightWindow_zero {T t : ℝ} (hT : 0 < T)
    (ht : t ∉ dyadicHeightSupport T) : heightWindow T t = 0 := by
  have hnot : ¬(T ≤ |t| ∧ |t| ≤ 2*T) := by
    rintro ⟨hl,hu⟩
    apply ht
    rcases le_total 0 t with hpos | hneg
    · left
      simpa only [Set.mem_Icc, abs_of_nonneg hpos] using And.intro hl hu
    · right
      rw [abs_of_nonpos hneg] at hl hu
      exact ⟨by linarith, by linarith⟩
  rcases lt_or_ge |t| T with hl | hl
  · have hsmall : |t/T| ≤ 1 := by rw [abs_div, abs_of_pos hT]; exact (div_le_one hT).mpr hl.le
    have hsmall' : |t/((3/2)*T)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < (3/2:ℝ)*T)]
      apply (div_le_one (by positivity)).mpr
      linarith
    simp only [heightWindow, heightPartitionBump_one hsmall,
      heightPartitionBump_one hsmall', sub_self, Complex.ofReal_zero]
  · have hu : 2*T < |t| := lt_of_not_ge (fun hu => hnot ⟨hl,hu⟩)
    have hlarge : 4/3 ≤ |t/T| := by
      rw [abs_div, abs_of_pos hT]
      apply (le_div_iff₀ hT).mpr
      linarith
    have hlarge' : 4/3 ≤ |t/((3/2)*T)| := by
      rw [abs_div, abs_of_pos (by positivity : 0 < (3/2:ℝ)*T)]
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    simp only [heightWindow, heightPartitionBump_zero hlarge,
      heightPartitionBump_zero hlarge', sub_self, Complex.ofReal_zero]

lemma heightWindow_telescope (T t : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, heightWindow (T*(3/2:ℝ)^j) t) =
      ((heightPartitionBump (t/(T*(3/2:ℝ)^n)) - heightPartitionBump (t/T) : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have he : (3/2:ℝ)*(T*(3/2:ℝ)^n) = T*(3/2:ℝ)^(n+1) := by rw [pow_succ]; ring
    simp only [heightWindow, he, Complex.ofReal_sub]
    ring

lemma cutoffHeightMultiplier_partition {S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (n : ℕ) (hn : 2*Real.pi*S ≤ T*(3/2:ℝ)^n) (t : ℝ) :
    cutoffHeightMultiplier S t =
      cutoffHeightMultiplier S t*(heightPartitionBump (t/T) : ℂ) +
        ∑ j ∈ Finset.range n,
          cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t := by
  rw [← Finset.mul_sum, heightWindow_telescope]
  by_cases ht : |t| ≤ 2*Real.pi*S
  · have hpos : 0 < T*(3/2:ℝ)^n := by positivity
    have hsmall : |t/(T*(3/2:ℝ)^n)| ≤ 1 := by
      rw [abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).mpr (ht.trans hn)
    rw [heightPartitionBump_one hsmall]
    push_cast
    ring
  · rw [cutoffHeightMultiplier_zero hS (le_of_lt (lt_of_not_ge ht))]
    simp

lemma integrable_cutoffHeightMultiplier_window {S : ℝ} (hS : 0 < S) (T : ℝ) :
    Integrable (fun t => cutoffHeightMultiplier S t*heightWindow T t) :=
  (cutoffHeightMultiplier_integrable hS).mul_bdd
    (heightWindow_smooth T).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (heightWindow_norm_le T))

lemma cutoffHeightMultiplier_integral_partition {S T B : ℝ}
    (hS : 0 < S) (hT : 0 < T) (n : ℕ) (hn : 2*Real.pi*S ≤ T*(3/2:ℝ)^n)
    (f : ℝ → ℂ) (hf : Continuous f) (hB : ∀ t, ‖f t‖ ≤ B) :
    (∫ t : ℝ, cutoffHeightMultiplier S t*f t) =
      (∫ t : ℝ, (cutoffHeightMultiplier S t*(heightPartitionBump (t/T):ℂ))*f t) +
        ∑ j ∈ Finset.range n, ∫ t : ℝ,
          (cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t)*f t := by
  have hlow : Integrable (fun t =>
      (cutoffHeightMultiplier S t*(heightPartitionBump (t/T):ℂ))*f t) := by
    apply Integrable.mul_bdd _ hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
    apply (cutoffHeightMultiplier_integrable hS).mul_bdd (c := 1)
    · exact (Complex.continuous_ofReal.comp
        (heightPartitionBump.continuous.comp (continuous_id.div_const T))).aestronglyMeasurable
    · filter_upwards with t
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg heightPartitionBump.nonneg] using
          (heightPartitionBump.le_one (x := t/T))
  have hpiece (j : ℕ) : Integrable (fun t =>
      (cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t)*f t) :=
    (integrable_cutoffHeightMultiplier_window hS _).mul_bdd hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
  calc
    _ = ∫ t : ℝ, (cutoffHeightMultiplier S t*(heightPartitionBump (t/T):ℂ))*f t +
        ∑ j ∈ Finset.range n,
          (cutoffHeightMultiplier S t*heightWindow (T*(3/2:ℝ)^j) t)*f t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [← Finset.sum_mul, ← add_mul, ← cutoffHeightMultiplier_partition hS hT n hn t]
    _ = _ := by
      rw [integral_add hlow (integrable_finsetSum _ (fun j _ => hpiece j)),
        integral_finsetSum _ (fun j _ => hpiece j)]

end CubicFirstMoment

end

end OAI
