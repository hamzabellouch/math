import Mathlib
import OAI.Probability.GaussianInformation.Kernel.MixedMoments

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Sphere
open KernelPotential.Geometry

noncomputable def unitVolume (d : ℕ) : Measure (Ambient d) :=
  (volume (ball (0 : Ambient d) 1))⁻¹ • volume

lemma unit_ball_pos (d : ℕ) : 0 < volume (ball (0 : Ambient d) 1) :=
  measure_ball_pos volume _ zero_lt_one

lemma unit_ball_ne_top (d : ℕ) : volume (ball (0 : Ambient d) 1) ≠ ∞ :=
  measure_ball_lt_top.ne

lemma unitVolume_ball (d : ℕ) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    unitVolume d (ball z r) = ENNReal.ofReal (r^d) := by
  rw [unitVolume,Measure.smul_apply,smul_eq_mul,volume.addHaar_ball_of_pos z hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [mul_left_comm, ENNReal.inv_mul_cancel (unit_ball_pos d).ne' (unit_ball_ne_top d),mul_one]

lemma measurable_radial (d : ℕ) : Measurable (@radial d) :=
  measurable_norm.inv.smul measurable_id

lemma sphereProbability_eq (d : ℕ) :
    sphereProbability d = ((unitVolume d).restrict (ball 0 1)).map radial := by
  simp only [sphereProbability,unitVolume,Measure.restrict_smul]

instance sphereProbability_probability (d : ℕ) : IsProbabilityMeasure (sphereProbability d) := by
  rw [sphereProbability_eq]
  have : IsProbabilityMeasure ((unitVolume d).restrict (ball 0 1)) := by
    constructor
    simp only [Measure.restrict_apply_univ, unitVolume_ball d _ zero_lt_one, one_pow, ENNReal.ofReal_one]
  exact Measure.isProbabilityMeasure_map_iff (measurable_radial d).aemeasurable |>.mpr inferInstance

lemma radial_rescale {d : ℕ} (x : Ambient d) : ‖x‖ • radial x = x := by
  by_cases hx : x = 0
  · simp [hx,radial]
  · simp only [radial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma norm_radial {d : ℕ} (x : Ambient d) (hx : x ≠ 0) : ‖radial x‖ = 1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma ae_unit_norm {d : ℕ} (hd : 0 < d) : ∀ᵐ s ∂sphereProbability d, ‖s‖ = 1 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have : Nontrivial (Ambient d) := inferInstance
  rw [sphereProbability_eq]
  apply (ae_map_iff (measurable_radial d).aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)).mpr
  have hz : ∀ᵐ x ∂((unitVolume d).restrict (ball 0 1)), x ≠ 0 := by
    have ha : ((unitVolume d).restrict (ball 0 1)) ≪ (volume : Measure (Ambient d)) :=
      Measure.absolutelyContinuous_restrict.trans Measure.smul_absolutelyContinuous
    apply ha.ae_le
    exact ae_iff.mpr (by simp)
  filter_upwards [hz] with x hx
  exact norm_radial x hx

lemma singleton_span_finrank_le {d : ℕ} (z : Ambient d) :
    Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))) ≤ 1 := by
  by_cases hz : z = 0
  · rw [hz,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]
    omega
  · exact (finrank_span_singleton hz).le

lemma preimage_cap_tube {d : ℕ} (z : Ambient d) {r : ℝ} (_hr : 0 < r) :
    radial ⁻¹' ball z r ∩ ball 0 1 ⊆
      {x | ‖x‖ ≤ 1 ∧ infDist x (Submodule.span ℝ ({z} : Set (Ambient d)) : Set (Ambient d)) ≤ r} := by
  intro x hx
  have hxn : ‖x‖ < 1 := by simpa using hx.2
  have hxz : dist (radial x) z < r := hx.1
  refine ⟨hxn.le, ?_⟩
  have hz : ‖x‖ • z ∈ Submodule.span ℝ ({z} : Set (Ambient d)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  apply (infDist_le_dist_of_mem hz).trans
  calc
    dist x (‖x‖ • z) = ‖x‖ * dist (radial x) z := by
      calc
        _ = dist (‖x‖ • radial x) (‖x‖ • z) := congrArg (fun y => dist y (‖x‖ • z)) (radial_rescale x).symm
        _ = _ := by rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    _ ≤ 1*r := mul_le_mul hxn.le hxz.le dist_nonneg (by norm_num)
    _ = r := one_mul _

lemma cap_bound {d : ℕ} (hd : 2 ≤ d) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    sphereProbability d (ball z r) ≤ ENNReal.ofReal ((9*3^d:ℝ)*r^(d-1)) := by
  by_cases hr1 : r ≤ 1
  · let V : AffineSubspace ℝ (Ambient d) := (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace
    have hdim : Module.finrank ℝ V.direction + ((d-2)+1) ≤ d := by
      have hz := singleton_span_finrank_le z
      change Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace.direction + _ ≤ d
      rw [Submodule.toAffineSubspace_direction]
      omega
    have ht := tube_ball_bound (unitVolume d) (a := d) (k := d-2) (B := 1) (R := 1)
      (by norm_num) (by norm_num) hr hr1 (fun z r hr => by simpa using (unitVolume_ball d z hr).le)
      V ⟨0,Submodule.zero_mem _⟩ hdim
    calc
      _ = unitVolume d (radial ⁻¹' ball z r ∩ ball 0 1) := by
        rw [sphereProbability_eq,Measure.map_apply (measurable_radial d) measurableSet_ball,
          Measure.restrict_apply ((measurable_radial d) measurableSet_ball)]
      _ ≤ unitVolume d {x | ‖x‖ ≤ 1 ∧ infDist x (V : Set (Ambient d)) ≤ 1*r} :=
        measure_mono (by
          change radial ⁻¹' ball z r ∩ ball 0 1 ⊆ {x | ‖x‖ ≤ 1 ∧
            infDist x (Submodule.span ℝ ({z} : Set (Ambient d)) : Set (Ambient d)) ≤ 1*r}
          simpa only [one_mul] using preimage_cap_tube z hr)
      _ ≤ ENNReal.ofReal (1 * 9^(Module.finrank ℝ V.direction) * 3^d * 1^d * r^((d-2)+1)) := ht
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (d-2)+1=d-1 by omega]
        simp only [one_mul,one_pow,mul_one]
        gcongr
        calc
          (9:ℝ)^(Module.finrank ℝ V.direction) ≤ 9^1 := by
            apply pow_le_pow_right₀ (by norm_num)
            change Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace.direction ≤ 1
            rw [Submodule.toAffineSubspace_direction]
            exact singleton_span_finrank_le z
          _ = 9 := pow_one _
  · apply (prob_le_one (μ := sphereProbability d)).trans
    apply ENNReal.one_le_ofReal.mpr
    have h3 : (1:ℝ) ≤ 3^d := one_le_pow₀ (by norm_num)
    have hrp : (1:ℝ) ≤ r^(d-1) := one_le_pow₀ (by linarith : (1:ℝ) ≤ r)
    nlinarith

end Sphere

end KernelPotential

end OAI
