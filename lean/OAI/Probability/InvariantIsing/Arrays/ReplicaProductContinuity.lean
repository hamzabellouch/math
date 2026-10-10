import OAI.Probability.InvariantIsing.Arrays.QuantileProductPath

namespace OAI

/-! The replica product is a bounded continuous function of the total
overlap when the synchronized group factors are bounded and continuous. -/

noncomputable section

open MeasureTheory IsingPerceptron Set

namespace InvariantIsing

lemma replicaProductFirst_eq_min (a b : ℝ → ℝ) (x y : ℝ) :
    replicaProductFirst a b x y = a y * b (min x y) := by
  unfold replicaProductFirst
  by_cases hyx : y < x
  · rw [ite_eq_left hyx, min_eq_right hyx.le]
  · rw [ite_eq_right hyx, min_eq_left (le_of_not_gt hyx)]

lemma replicaProductSecond_eq_max (a b : ℝ → ℝ) (x y : ℝ) :
    replicaProductSecond a b x y = a x * (b (max x y) - b x) := by
  unfold replicaProductSecond
  by_cases hxy : x < y
  · rw [ite_eq_left hxy, max_eq_right hxy.le]
  · rw [ite_eq_right hxy, max_eq_left (le_of_not_gt hxy), sub_self, mul_zero]

lemma continuous_replicaProductFirst {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z : ℝ × ℝ => replicaProductFirst a b z.1 z.2) := by
  simp_rw [replicaProductFirst_eq_min]
  exact (ha.comp continuous_snd).mul (hb.comp (continuous_fst.min continuous_snd))

lemma continuous_replicaProductSecond {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z : ℝ × ℝ => replicaProductSecond a b z.1 z.2) := by
  simp_rw [replicaProductSecond_eq_max]
  exact (ha.comp continuous_fst).mul
    ((hb.comp (continuous_fst.max continuous_snd)).sub (hb.comp continuous_fst))

def replicaProductKernel (ζ : Measure ℝ) (a b : ℝ → ℝ) (r : ℝ) : ℝ :=
  (∫ y, replicaProductFirst a b r y + replicaProductSecond a b r y ∂ζ) + a r * b r

lemma replicaProductKernel_abs_le (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (a b : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (r : ℝ) :
    |replicaProductKernel ζ a b r| ≤ 4 * (A * B) := by
  have hi : |∫ y, replicaProductFirst a b r y + replicaProductSecond a b r y ∂ζ| ≤ 3 * (A * B) := by
    apply abs_integral_le_const_of_bound
      (((measurable_replicaProductFirst ha hb).add (measurable_replicaProductSecond ha hb)).comp
        (measurable_const.prodMk measurable_id))
    intro y
    exact (abs_add_le _ _).trans ((add_le_add (replicaProductFirst_abs_le hA haB hbB r y)
      (replicaProductSecond_abs_le hA hB haB hbB r y)).trans_eq (by ring))
  have hab : |a r * b r| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (haB r) (hbB r) (abs_nonneg _) hA
  exact (abs_add_le _ _).trans ((add_le_add hi hab).trans_eq (by ring))

lemma continuous_replicaProductKernel (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) :
    Continuous (replicaProductKernel ζ a b) := by
  have hc := (continuous_replicaProductFirst ha hb).add (continuous_replicaProductSecond ha hb)
  have hi : Continuous (fun r => ∫ y, replicaProductFirst a b r y + replicaProductSecond a b r y ∂ζ) := by
    apply continuous_of_dominated (bound := fun _ => 3 * (A * B))
    · intro r
      exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro r
      exact ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]
        exact (abs_add_le _ _).trans ((add_le_add (replicaProductFirst_abs_le hA haB hbB r y)
          (replicaProductSecond_abs_le hA hB haB hbB r y)).trans_eq (by ring))
    · exact integrable_const _
    · exact ae_of_all _ fun y => hc.comp (continuous_id.prodMk continuous_const)
  exact hi.add (ha.mul hb)

def replicaProductValue (ζ : Measure ℝ) (da db : ℝ) (a b : ℝ → ℝ) (r : ℝ) : ℝ :=
  da * b r + a r * db - replicaProductKernel ζ a b r

lemma replicaProductValue_abs_le (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (da db : ℝ) (a b : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (r : ℝ) :
    |replicaProductValue ζ da db a b r| ≤ |da| * B + A * |db| + 4 * (A * B) := by
  have h1 : |da * b r| ≤ |da| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbB r) (abs_nonneg _)
  have h2 : |a r * db| ≤ A * |db| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (haB r) (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add h1 h2))
    (replicaProductKernel_abs_le ζ a b ha hb hA hB haB hbB r))

lemma continuous_replicaProductValue (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (da db : ℝ) (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) :
    Continuous (replicaProductValue ζ da db a b) :=
  ((hb.const_mul da).add (ha.mul_const db)).sub
    (continuous_replicaProductKernel ζ a b ha hb hA hB haB hbB)

lemma replicaProductPath_eq_value (p : OverlapPath) (ζ : Measure ℝ)
    (hl : pathMeasure.map p = ζ) (da db : ℝ) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    replicaProductPath da (fun u => a (p u)) db (fun u => b (p u)) s =
      replicaProductValue ζ da db a b (p s) := by
  rw [replicaProductPath_eq_quantile_kernel p a b ha hb hA haB hbB da db hs]
  unfold replicaProductValue replicaProductKernel
  rw [← hl]
  have hm : StronglyMeasurable (fun y =>
      replicaProductFirst a b (p s) y + replicaProductSecond a b (p s) y) :=
    ((((measurable_replicaProductFirst ha hb).add (measurable_replicaProductSecond ha hb)).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable)
  rw [integral_map_of_stronglyMeasurable p.measurable hm]

end InvariantIsing

end

end OAI
