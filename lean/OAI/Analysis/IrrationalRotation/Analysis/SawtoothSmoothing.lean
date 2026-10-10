import OAI.Analysis.IrrationalRotation.Model.SawtoothSmoothing
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set

theorem intervalIntegrable_fract (a b : ℝ) :
    IntervalIntegrable Int.fract volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
  · exact measurable_fract.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      change ‖Int.fract x‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      exact (Int.fract_lt_one x).le)

theorem fract_fract_add (u a : ℝ) :
    Int.fract (Int.fract u + a) = Int.fract (u + a) := by
  have hu : u + a = (Int.fract u + a) + (⌊u⌋ : ℝ) := by
    have := Int.fract_add_floor u
    linarith
  rw [hu, Int.fract_add_intCast]

theorem floor_drop_eq_sawtooth_difference (u a : ℝ) :
    (⌊Int.fract u + a⌋ : ℝ) = a + Int.fract u - Int.fract (u + a) := by
  have ha := Int.floor_add_fract (Int.fract u + a)
  rw [fract_fract_add] at ha
  linarith

theorem smoothedDrop_eq_add_coboundary (C a δ u : ℝ) :
    smoothedDrop C a δ u = C * (⌊Int.fract u + a⌋ : ℝ) +
      smoothingTransfer C δ u - smoothingTransfer C δ (u + a) := by
  rw [floor_drop_eq_sawtooth_difference]
  unfold smoothedDrop smoothingTransfer
  ring

theorem smoothSawtooth_periodic (δ : ℝ) :
    Function.Periodic (smoothSawtooth δ) 1 := by
  intro u
  unfold smoothSawtooth
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have h : u + 1 + t = (u + t) + 1 := by ring
  change Int.fract (u + 1 + t) = Int.fract (u + t)
  rw [h, Int.fract_add_one]

theorem continuous_smoothSawtooth (δ : ℝ) : Continuous (smoothSawtooth δ) := by
  have hc := intervalIntegral.continuous_primitive intervalIntegrable_fract 0
  have heq (u : ℝ) : smoothSawtooth δ u =
      (2 * δ)⁻¹ * ((∫ t in 0..u + δ, Int.fract t) -
        ∫ t in 0..u - δ, Int.fract t) := by
    unfold smoothSawtooth
    rw [intervalIntegral.integral_comp_add_left]
    have ht := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fract 0 (u - δ))
      (intervalIntegrable_fract (u - δ) (u + δ))
    congr 1
    change (∫ t in u - δ..u + δ, Int.fract t) = _
    linarith
  have hf : smoothSawtooth δ = fun u =>
      (2 * δ)⁻¹ * ((∫ t in 0..u + δ, Int.fract t) -
        ∫ t in 0..u - δ, Int.fract t) := funext heq
  rw [hf]
  exact continuous_const.mul ((hc.comp (continuous_id.add_const δ)).sub
    (hc.comp (continuous_id.sub continuous_const)))

theorem continuous_smoothedDrop (C a δ : ℝ) : Continuous (smoothedDrop C a δ) := by
  unfold smoothedDrop
  exact continuous_const.mul ((continuous_const.add (continuous_smoothSawtooth δ)).sub
    ((continuous_smoothSawtooth δ).comp (continuous_id.add_const a)))

theorem intervalIntegrable_fract_add (u a b : ℝ) :
    IntervalIntegrable (fun t => Int.fract (u + t)) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
  · exact (measurable_const.add measurable_id).fract.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      change ‖Int.fract (u + t)‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le)

theorem smoothedDrop_eq_average (C a δ u : ℝ) (hδ : δ ≠ 0) :
    smoothedDrop C a δ u = C * (2 * δ)⁻¹ *
      ∫ t in -δ..δ, (⌊Int.fract (u + t) + a⌋ : ℝ) := by
  have hiu := intervalIntegrable_fract_add u (-δ) δ
  have hiua := intervalIntegrable_fract_add (u + a) (-δ) δ
  have hi : (∫ t in -δ..δ, (⌊Int.fract (u + t) + a⌋ : ℝ)) =
      (2 * δ) * a + (∫ t in -δ..δ, Int.fract (u + t)) -
        (∫ t in -δ..δ, Int.fract (u + a + t)) := by
    calc
      _ = ∫ t in -δ..δ, a + Int.fract (u + t) - Int.fract (u + a + t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change (⌊Int.fract (u + t) + a⌋ : ℝ) = _
        rw [floor_drop_eq_sawtooth_difference]
        congr 2
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hiu) hiua,
          intervalIntegral.integral_add intervalIntegrable_const hiu,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  rw [hi]
  unfold smoothedDrop smoothSawtooth
  field_simp

theorem smoothedDrop_nonneg {C a δ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hδ : 0 < δ) (u : ℝ) : 0 ≤ smoothedDrop C a δ u := by
  rw [smoothedDrop_eq_average C a δ u hδ.ne']
  apply mul_nonneg
  · positivity
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact_mod_cast Int.floor_nonneg.mpr (add_nonneg (Int.fract_nonneg _) ha)

theorem smoothSawtooth_eq_fract_of_middle {δ u : ℝ} (hδ : 0 < δ)
    (hlo : δ ≤ Int.fract u) (hhi : Int.fract u + δ < 1) :
    smoothSawtooth δ u = Int.fract u := by
  have hi : (∫ t in -δ..δ, Int.fract (u + t)) =
      ∫ t in -δ..δ, Int.fract u + t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -δ ≤ δ)] at ht
    change Int.fract (u + t) = Int.fract u + t
    rw [← fract_fract_add]
    apply Int.fract_eq_self.mpr
    constructor <;> linarith [ht.1, ht.2]
  unfold smoothSawtooth
  rw [hi, intervalIntegral.integral_add
    (f := fun _ : ℝ => Int.fract u) (g := fun t : ℝ => t)
    intervalIntegrable_const (continuous_id.intervalIntegrable (-δ) δ),
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem smoothingTransfer_eq_zero_of_middle {δ u : ℝ} (C : ℝ)
    (hδ : 0 < δ) (hlo : δ ≤ Int.fract u) (hhi : Int.fract u + δ < 1) :
    smoothingTransfer C δ u = 0 := by
  simp [smoothingTransfer, smoothSawtooth_eq_fract_of_middle hδ hlo hhi]

theorem integral_smoothedDrop (C a δ : ℝ) :
    (∫ u in (0 : ℝ)..1, smoothedDrop C a δ u) = C * a := by
  have hs := continuous_smoothSawtooth δ
  have hshift : (∫ u in (0 : ℝ)..1, smoothSawtooth δ (u + a)) =
      ∫ u in (0 : ℝ)..1, smoothSawtooth δ u := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm (1 : ℝ) a] using
      (smoothSawtooth_periodic δ).intervalIntegral_add_eq a 0
  unfold smoothedDrop
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (f := fun u : ℝ => a + smoothSawtooth δ u)
      (g := fun u : ℝ => smoothSawtooth δ (u + a))
      (intervalIntegrable_const.add (hs.intervalIntegrable 0 1))
      ((hs.comp (continuous_id.add_const a)).intervalIntegrable 0 1),
    intervalIntegral.integral_add
      (f := fun _ : ℝ => a) (g := smoothSawtooth δ)
      intervalIntegrable_const (hs.intervalIntegrable 0 1),
    intervalIntegral.integral_const, hshift]
  simp

theorem smoothedDrop_eq_zero_of_middle {a δ u : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hlo : δ ≤ Int.fract u)
    (hhi : Int.fract u + a + δ < 1) : smoothedDrop C a δ u = 0 := by
  rw [smoothedDrop_eq_average C a δ u hδ.ne']
  have hi : (∫ t in -δ..δ, (⌊Int.fract (u + t) + a⌋ : ℝ)) = 0 := by
    calc
      _ = ∫ _t in -δ..δ, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : -δ ≤ δ)] at ht
        have hf : Int.fract (u + t) = Int.fract u + t := by
          rw [← fract_fract_add]
          apply Int.fract_eq_self.mpr
          constructor <;> linarith [ht.1, ht.2]
        have hz : ⌊Int.fract (u + t) + a⌋ = 0 := by
          rw [hf, Int.floor_eq_iff]
          constructor <;> norm_num <;> linarith [ht.1, ht.2]
        change (⌊Int.fract (u + t) + a⌋ : ℝ) = 0
        rw [hz, Int.cast_zero]
      _ = 0 := by simp
  rw [hi, mul_zero]

theorem measure_smoothingTransfer_support_le {δ : ℝ} (C : ℝ) (hδ : 0 < δ) :
    volume {u : ℝ | u ∈ Ico 0 1 ∧ smoothingTransfer C δ u ≠ 0} ≤
      ENNReal.ofReal (2 * δ) := by
  have hsub : {u : ℝ | u ∈ Ico 0 1 ∧ smoothingTransfer C δ u ≠ 0} ⊆
      Icc 0 δ ∪ Icc (1 - δ) 1 := by
    intro u hu
    by_contra hout
    have hfrac : Int.fract u = u := Int.fract_eq_self.mpr hu.1
    have hleft : δ < u := by
      by_contra hn
      exact hout (Or.inl ⟨hu.1.1, le_of_not_gt hn⟩)
    have hright : u < 1 - δ := by
      by_contra hn
      exact hout (Or.inr ⟨le_of_not_gt hn, hu.1.2.le⟩)
    apply hu.2
    apply smoothingTransfer_eq_zero_of_middle C hδ
    · simpa [hfrac] using hleft.le
    · rw [hfrac]
      linarith
  calc
    _ ≤ volume (Icc 0 δ ∪ Icc (1 - δ) 1) := measure_mono hsub
    _ ≤ volume (Icc 0 δ) + volume (Icc (1 - δ) 1) := measure_union_le _ _
    _ = ENNReal.ofReal δ + ENNReal.ofReal δ := by simp
    _ = ENNReal.ofReal (2 * δ) := by
      rw [← ENNReal.ofReal_add hδ.le hδ.le]
      congr 1
      ring

theorem measure_smoothedDrop_support_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) :
    volume {u : ℝ | u ∈ Ico 0 1 ∧ smoothedDrop C a δ u ≠ 0} ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hsub : {u : ℝ | u ∈ Ico 0 1 ∧ smoothedDrop C a δ u ≠ 0} ⊆
      Icc 0 δ ∪ Icc (1 - a - δ) 1 := by
    intro u hu
    by_contra hout
    have hfrac : Int.fract u = u := Int.fract_eq_self.mpr hu.1
    have hleft : δ < u := by
      by_contra hn
      exact hout (Or.inl ⟨hu.1.1, le_of_not_gt hn⟩)
    have hright : u < 1 - a - δ := by
      by_contra hn
      exact hout (Or.inr ⟨le_of_not_gt hn, hu.1.2.le⟩)
    apply hu.2
    apply smoothedDrop_eq_zero_of_middle C ha hδ
    · simpa [hfrac] using hleft.le
    · rw [hfrac]
      linarith
  calc
    _ ≤ volume (Icc 0 δ ∪ Icc (1 - a - δ) 1) := measure_mono hsub
    _ ≤ volume (Icc 0 δ) + volume (Icc (1 - a - δ) 1) := measure_union_le _ _
    _ = ENNReal.ofReal δ + ENNReal.ofReal (a + δ) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      congr 1 <;> congr 1 <;> ring
    _ = ENNReal.ofReal (a + 2 * δ) := by
      rw [← ENNReal.ofReal_add hδ.le (by linarith)]
      congr 1
      ring

end InvariantProjection.Continuity

end OAI
