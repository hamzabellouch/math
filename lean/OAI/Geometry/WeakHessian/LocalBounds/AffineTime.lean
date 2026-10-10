import Mathlib
import OAI.Geometry.WeakHessian.Model

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def affineTime (a b u : Time) : Time :=
  ⟨(1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ), by
    constructor
    · exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr u.property.2) a.property.1)
        (mul_nonneg u.property.1 b.property.1)
    · have h₁ := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr a.property.2)
      have h₂ := mul_nonneg u.property.1 (sub_nonneg.mpr b.property.2)
      nlinarith⟩

@[simp] theorem affineTime_zero (a b : Time) : affineTime a b timeZero = a := by
  apply Subtype.ext
  simp only [affineTime, timeZero, sub_zero, one_mul, zero_mul, add_zero]

@[simp] theorem affineTime_one (a b : Time) : affineTime a b timeOne = b := by
  apply Subtype.ext
  simp only [affineTime, timeOne, sub_self, zero_mul, one_mul, zero_add]

lemma continuous_affineTime (a b : Time) : Continuous (affineTime a b) := by
  exact (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _

def restrictCurve (a b : Time) (γ : Curve X) : Curve X :=
  γ.comp ⟨affineTime a b, continuous_affineTime a b⟩

lemma continuous_restrictCurve (a b : Time) : Continuous (restrictCurve (X := X) a b) := by
  exact ContinuousMap.continuous_precomp _

@[simp] lemma restrictCurve_zero (a b : Time) (γ : Curve X) :
    restrictCurve a b γ timeZero = γ a := by simp [restrictCurve]

@[simp] lemma restrictCurve_one (a b : Time) (γ : Curve X) :
    restrictCurve a b γ timeOne = γ b := by simp [restrictCurve]

lemma clampTime_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (clampTime t : ℝ) = t := by
  simp only [clampTime, min_eq_right ht.2, max_eq_right ht.1]

lemma evalReal_restrictCurve {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (a b : Time) (γ : Curve X) :
    evalReal (restrictCurve a b γ) t = evalReal γ ((a : ℝ) + ((b : ℝ) - a) * t) := by
  have hv : (affineTime a b (clampTime t) : ℝ) = (a : ℝ) + ((b : ℝ) - a) * t := by
    simp only [affineTime, clampTime_of_mem ht]
    ring
  have hh : (a : ℝ) + ((b : ℝ) - a) * t ∈ Set.Icc (0 : ℝ) 1 :=
    hv ▸ (affineTime a b (clampTime t)).property
  change γ (affineTime a b (clampTime t)) = γ (clampTime _)
  congr 1
  apply Subtype.ext
  rw [hv, clampTime_of_mem hh]

def affineHomeomorph (a c : ℝ) (hc : c ≠ 0) : ℝ ≃ₜ ℝ :=
  (Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addLeft a)

@[simp] lemma affineHomeomorph_apply (a c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    affineHomeomorph a c hc t = a + c * t := rfl

lemma metricSpeed_restrictCurve (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    metricSpeed (restrictCurve a b γ) t =
      ENNReal.ofReal ((b : ℝ) - a) * metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t) := by
  let c : ℝ := (b : ℝ) - a
  have hc : 0 < c := sub_pos.mpr hab
  let e := affineHomeomorph (a : ℝ) c hc.ne'
  have hnh : Filter.map e (𝓝[≠] t) = 𝓝[≠] (e t) := e.map_punctured_nhds_eq t
  have heq : (fun s : ℝ => ENNReal.ofReal
      (dist (evalReal (restrictCurve a b γ) s) (evalReal (restrictCurve a b γ) t) / |s - t|))
      =ᶠ[𝓝[≠] t] (fun s => ENNReal.ofReal c * ENNReal.ofReal
        (dist (evalReal γ (e s)) (evalReal γ (e t)) / |e s - e t|)) := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2),
      self_mem_nhdsWithin] with s hs hst
    rw [evalReal_restrictCurve ⟨hs.1.le, hs.2.le⟩,
      evalReal_restrictCurve ⟨ht.1.le, ht.2.le⟩]
    change ENNReal.ofReal (dist (evalReal γ (e s)) (evalReal γ (e t)) / |s - t|) = _
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    have hd : |e s - e t| = c * |s - t| := by
      dsimp [e, affineHomeomorph]
      change |(a : ℝ) + c * s - ((a : ℝ) + c * t)| = c * |s - t|
      rw [show (a : ℝ) + c * s - ((a : ℝ) + c * t) = c * (s - t) by ring,
        abs_mul, abs_of_pos hc]
    rw [hd]
    field_simp
  unfold metricSpeed
  rw [Filter.limsup_congr heq, ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr 1
  change Filter.limsup (fun s => ENNReal.ofReal
    (dist (evalReal γ (e s)) (evalReal γ (e t)) / |e s - e t|)) (𝓝[≠] t) =
    Filter.limsup (fun s => ENNReal.ofReal
      (dist (evalReal γ s) (evalReal γ (e t)) / |s - e t|)) (𝓝[≠] (e t))
  rw [← hnh]
  rfl

lemma map_affineHomeomorph_volume (a c : ℝ) (hc : 0 < c) :
    Measure.map (affineHomeomorph a c hc.ne') volume =
      (ENNReal.ofReal c)⁻¹ • (volume : Measure ℝ) := by
  change Measure.map ((fun t : ℝ => a + t) ∘ (fun t : ℝ => c * t)) volume = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left hc.ne',
    Measure.map_smul _ (by fun_prop), map_add_left_eq_self, abs_of_pos (inv_pos.mpr hc),
    ENNReal.ofReal_inv_of_pos hc]

lemma affineHomeomorph_preimage_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ) :
    affineHomeomorph a c hc.ne' ⁻¹' Set.Icc (a + c * s) (a + c * t) = Set.Icc s t := by
  ext u
  simp only [Set.mem_preimage, Set.mem_Icc, affineHomeomorph_apply, add_le_add_iff_left,
    mul_le_mul_iff_right₀ hc]

lemma lintegral_affine_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Icc s t, f (a + c * r)) =
      (ENNReal.ofReal c)⁻¹ * ∫⁻ r in Set.Icc (a + c * s) (a + c * t), f r := by
  let e := affineHomeomorph a c hc.ne'
  have hre : (Measure.map e volume).restrict (Set.Icc (a + c * s) (a + c * t)) =
      Measure.map e (volume.restrict (Set.Icc s t)) := by
    rw [e.measurableEmbedding.restrict_map, affineHomeomorph_preimage_Icc a c hc]
  calc
    (∫⁻ r in Set.Icc s t, f (a + c * r)) =
        ∫⁻ r, f r ∂Measure.map e (volume.restrict (Set.Icc s t)) :=
      (e.measurableEmbedding.lintegral_map f).symm
    _ = ∫⁻ r, f r ∂(Measure.map e volume).restrict (Set.Icc (a + c * s) (a + c * t)) := by rw [hre]
    _ = _ := by rw [map_affineHomeomorph_volume a c hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

lemma coe_affineTime (a b u : Time) :
    (affineTime a b u : ℝ) = (a : ℝ) + ((b : ℝ) - a) * (u : ℝ) := by
  simp only [affineTime]
  ring

lemma lintegral_scaled_affine_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Icc s t, ENNReal.ofReal c * f (a + c * r)) =
      ∫⁻ r in Set.Icc (a + c * s) (a + c * t), f r := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_affine_Icc a c hc,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, one_mul]

lemma lintegral_scaled_sq_affine_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Icc s t, (ENNReal.ofReal c * f (a + c * r)) ^ 2) =
      ENNReal.ofReal c * ∫⁻ r in Set.Icc (a + c * s) (a + c * t), (f r) ^ 2 := by
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness),
    lintegral_affine_Icc a c hc s t (fun r => f r ^ 2), pow_two]
  calc
    _ = ENNReal.ofReal c * (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹) *
        ∫⁻ r in Set.Icc (a + c * s) (a + c * t), f r ^ 2 := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, mul_one]

lemma IsAC2.restrictCurve {γ : Curve X} (hγ : IsAC2 γ) (a b : Time)
    (hab : (a : ℝ) < b) : IsAC2 (restrictCurve a b γ) := by
  obtain ⟨u, hum, hue, hub⟩ := hγ
  let c : ℝ := (b : ℝ) - a
  have hc : 0 < c := sub_pos.mpr hab
  refine ⟨fun t => ENNReal.ofReal c * u ((a : ℝ) + c * t),
    measurable_const.mul (hum.comp (by fun_prop)), ?_, ?_⟩
  · rw [lintegral_scaled_sq_affine_Icc _ _ hc]
    have hends : (a : ℝ) + c * 0 = a ∧ (a : ℝ) + c * 1 = b := by
      dsimp [c]
      constructor <;> ring
    rw [hends.1, hends.2]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact (lintegral_mono_set (Set.Icc_subset_Icc a.property.1 b.property.2)).trans_lt hue
  · intro s t hst
    have hst' : (affineTime a b s : ℝ) ≤ affineTime a b t := by
      rw [coe_affineTime, coe_affineTime]
      dsimp [c] at hc
      gcongr
    calc
      edist (WeakHessian.restrictCurve a b γ s) (WeakHessian.restrictCurve a b γ t) =
          edist (γ (affineTime a b s)) (γ (affineTime a b t)) := rfl
      _ ≤ ∫⁻ r in Set.Icc (affineTime a b s : ℝ) (affineTime a b t : ℝ), u r :=
        hub _ _ hst'
      _ = ∫⁻ r in Set.Icc (s : ℝ) (t : ℝ), ENNReal.ofReal c * u ((a : ℝ) + c * r) := by
        simpa only [coe_affineTime] using
          (lintegral_scaled_affine_Icc (a : ℝ) c hc (s : ℝ) (t : ℝ) u).symm

lemma ae_metricSpeed_restrictCurve (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X) :
    (fun t => metricSpeed (restrictCurve a b γ) t) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun t => ENNReal.ofReal ((b : ℝ) - a) *
        metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t)) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht =>
    metricSpeed_restrictCurve a b hab γ ht)

lemma kineticEnergy_restrictCurve (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed (restrictCurve a b γ) t ^ 2) =
      ENNReal.ofReal ((b : ℝ) - a) * ∫⁻ t in Set.Icc (a : ℝ) b, metricSpeed γ t ^ 2 := by
  have heq : (fun t => metricSpeed (restrictCurve a b γ) t ^ 2) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun t => (ENNReal.ofReal ((b : ℝ) - a) * metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t)) ^ 2) :=
    (ae_metricSpeed_restrictCurve a b hab γ).pow_const 2
  rw [lintegral_congr_ae heq, lintegral_scaled_sq_affine_Icc _ _ (sub_pos.mpr hab)]
  rw [show (a : ℝ) + ((b : ℝ) - a) * 0 = a by ring,
    show (a : ℝ) + ((b : ℝ) - a) * 1 = b by ring]

end WeakHessian

end
end InlinedFile0

end OAI
