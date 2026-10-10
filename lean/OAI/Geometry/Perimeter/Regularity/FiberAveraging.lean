import OAI.Geometry.Perimeter.Regularity.EllipticLocality

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution
namespace RPISingularHarnack
open RPI.Boundary

def normalFiberAverage {n : ℕ} (v : Euc n) (f : Euc n → ℝ) (x : Euc n) : ℝ :=
  ∫ s : ℝ, f (x+s•v)

theorem normalFiberAverage_stronglyMeasurable {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (v : Euc n) : StronglyMeasurable (normalFiberAverage v f) := by
  apply StronglyMeasurable.integral_prod_right
  exact (hf.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable).stronglyMeasurable

theorem normalFiberAverage_add_smul {n : ℕ} (v : Euc n) (f : Euc n → ℝ)
    (x : Euc n) (t : ℝ) :
    normalFiberAverage v f (x+t•v) = normalFiberAverage v f x := by
  unfold normalFiberAverage
  have heq : (fun s : ℝ ↦ f (x+t•v+s•v)) = (fun s : ℝ ↦ f (x+(s+t)•v)) := by
    funext s
    congr 1
    rw [add_smul]
    abel
  rw [heq]
  exact integral_add_right_eq_self (fun s : ℝ ↦ f (x+s•v)) t

theorem fiber_support_subset_interval {n : ℕ} {f : Euc n → ℝ}
    {v : Euc n} (hv : ‖v‖ = 1) {R : ℝ}
    (hs : Function.support f ⊆ Metric.ball 0 R) (x : Euc n) :
    Function.support (fun s : ℝ ↦ f (x+s•v)) ⊆ Icc (-(R+‖x‖)) (R+‖x‖) := by
  intro s hs'
  have hx := hs hs'
  rw [Metric.mem_ball, dist_zero_right] at hx
  have he : |s| = ‖s•v‖ := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
  have hl : |s| ≤ R+‖x‖ := by
    rw [he]
    calc
      ‖s•v‖ = ‖(x+s•v)-x‖ := by congr 1; abel
      _ ≤ ‖x+s•v‖+‖x‖ := norm_sub_le _ _
      _ ≤ R+‖x‖ := by linarith
  exact abs_le.mp hl

theorem integrable_fiber_of_bounded {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) {v : Euc n} (hv : ‖v‖ = 1) {R : ℝ}
    (hs : Function.support f ⊆ Metric.ball 0 R) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) (x : Euc n) :
    Integrable (fun s : ℝ ↦ f (x+s•v)) volume := by
  let I := Icc (-(R+‖x‖)) (R+‖x‖)
  have hI : Integrable (I.indicator (fun _ ↦ C)) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply hI.mono' (hf.comp (continuous_const.add (continuous_id.smul continuous_const)).measurable).aestronglyMeasurable
  apply ae_of_all
  intro s
  by_cases hsI : s ∈ I
  · simpa [hsI] using hb (x+s•v)
  · rw [indicator_of_notMem hsI]
    have hz : f (x+s•v) = 0 := by
      by_contra hz
      exact hsI (fiber_support_subset_interval hv hs x hz)
    simp [hz]

theorem normalFiberAverage_translation_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) {v : Euc n} (hv : ‖v‖ = 1) {R : ℝ} (hR : 0 < R)
    (hs : Function.support f ⊆ Metric.ball 0 R) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) {S : ℝ} (hS : 0 < S) (w : Euc n) :
    (∫⁻ x in Metric.ball (0:Euc n) S,
      ‖normalFiberAverage v f (x+w)-normalFiberAverage v f x‖ₑ) ≤
        ENNReal.ofReal (2*(R+S+‖w‖)) * ∫⁻ x, ‖f (x+w)-f x‖ₑ := by
  let T := R+S+‖w‖
  have hT : 0 < T := add_pos_of_pos_of_nonneg (add_pos hR hS) (norm_nonneg w)
  let I := Icc (-T) T
  let B := Metric.ball (0:Euc n) S
  have hxI (x : Euc n) (hx : x ∈ B) :
      Function.support (fun s : ℝ ↦ ‖f (x+w+s•v)-f (x+s•v)‖ₑ) ⊆ I := by
    intro s hs'
    have hx' : ‖x‖ < S := by simpa only [B, Metric.mem_ball, dist_zero_right] using hx
    have hzero (y : Euc n) (hy : ‖y‖ ≤ S+‖w‖) (hns : s ∉ I) : f (y+s•v) = 0 := by
      by_contra hz
      have ht := fiber_support_subset_interval hv hs y hz
      exact hns (Icc_subset_Icc (by dsimp [T]; linarith) (by dsimp [T]; linarith) ht)
    by_contra hns
    have h₁ := hzero (x+w) ((norm_add_le x w).trans (by linarith)) hns
    have h₂ := hzero x (hx'.le.trans (le_add_of_nonneg_right (norm_nonneg w))) hns
    simp only [Function.mem_support, ne_eq, h₁, h₂, sub_self, enorm_zero, not_true_eq_false] at hs'
  have hm : Measurable (fun p : Euc n × ℝ ↦ ‖f (p.1+w+p.2•v)-f (p.1+p.2•v)‖ₑ) :=
    ((hf.comp ((continuous_fst.add continuous_const).add
       (continuous_snd.smul continuous_const)).measurable).sub
      (hf.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable)).enorm
  calc
    _ ≤ ∫⁻ x in B, ∫⁻ s in I, ‖f (x+w+s•v)-f (x+s•v)‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [normalFiberAverage, normalFiberAverage,
        ← integral_sub (integrable_fiber_of_bounded hf hv hs hb (x+w))
          (integrable_fiber_of_bounded hf hv hs hb x)]
      rw [setLIntegral_eq_of_support_subset (hxI x hx)]
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ∫⁻ s in I, ‖f (x+w+s•v)-f (x+s•v)‖ₑ :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ s in I, ∫⁻ x, ‖f (x+w+s•v)-f (x+s•v)‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ENNReal.ofReal (2*T) * ∫⁻ x, ‖f (x+w)-f x‖ₑ := by
      have he (s : ℝ) : (∫⁻ x, ‖f (x+w+s•v)-f (x+s•v)‖ₑ) =
          ∫⁻ x, ‖f (x+w)-f x‖ₑ := by
        have heq : (fun x ↦ ‖f (x+w+s•v)-f (x+s•v)‖ₑ) =
            (fun x ↦ ‖f ((x+s•v)+w)-f (x+s•v)‖ₑ) := by
          funext x
          congr 3
          abel
        rw [heq]
        exact lintegral_add_right_eq_self (fun x : Euc n ↦ ‖f (x+w)-f x‖ₑ) (s•v)
      simp_rw [he]
      simp only [lintegral_const, Measure.restrict_apply_univ, I]
      rw [← uIcc_of_le (show -T ≤ T by linarith [hT]), Real.volume_interval,
        sub_neg_eq_add, ← two_mul, abs_of_pos (mul_pos (by norm_num) hT), mul_comm]

end RPISingularHarnack

end

end OAI
