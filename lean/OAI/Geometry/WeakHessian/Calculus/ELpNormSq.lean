import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.L2GradientGraph
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApprox

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma eLpNorm_sq_eq_lintegral (f : X → ℝ) (hf : AEStronglyMeasurable f m) :
    eLpNorm f 2 m ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := m) (f := f) (p := 2) (by norm_num) hf
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_natCast] at h
  simpa only [ENNReal.rpow_two] using h

lemma eLpNorm_localSlope_sq {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    eLpNorm (fun x => (localSlope f x).toReal) 2 m ^ 2 =
      ∫⁻ x, localSlope f x ^ 2 ∂m := by
  rw [eLpNorm_sq_eq_lintegral _
    (measurable_localSlope hf.continuous).ennreal_toReal.aestronglyMeasurable]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (lt_of_le_of_lt (localSlope_le_lipschitz hf x) ENNReal.coe_lt_top).ne]

lemma memLp_localSlope_of_lintegral_lt_top {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (h : (∫⁻ x, localSlope f x ^ 2 ∂m) < ∞) :
    MemLp (fun x => (localSlope f x).toReal) 2 m := by
  rw [← eLpNorm_localSlope_sq hf, ENNReal.pow_lt_top_iff] at h
  exact h.resolve_right (by omega)

omit [BorelSpace X] in
lemma norm_localSlope_toLp_sq {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (h : MemLp (fun x => (localSlope f x).toReal) 2 m) :
    ENNReal.ofReal (‖h.toLp (fun x => (localSlope f x).toReal)‖ ^ 2) =
      ∫⁻ x, localSlope f x ^ 2 ∂m := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def,
    eLpNorm_congr_ae h.coeFn_toLp, eLpNorm_sq_eq_lintegral _ h.aestronglyMeasurable]
  apply lintegral_congr
  intro point
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal
      (lt_of_le_of_lt (localSlope_le_lipschitz hf point) ENNReal.coe_lt_top).ne]


omit [BorelSpace X] in
lemma half_lintegral_localSlope_eq {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (h : MemLp (fun x => (localSlope f x).toReal) 2 m) :
    (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope f x ^ 2 ∂m) =
      ENNReal.ofReal (‖h.toLp (fun x => (localSlope f x).toReal)‖ ^ 2 / 2) := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    norm_localSlope_toLp_sq hf]
  norm_num only [ENNReal.ofReal_ofNat]
  exact mul_comm _ _

lemma lipschitz_mem_upperGradient_sublevel (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hf2 : MemLp f 2 m)
    {B : ℝ} (hB : 0 ≤ B)
    (he : (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope f x ^ 2 ∂m) ≤
      ENNReal.ofReal (B ^ 2 / 2)) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m (hf2.toLp f) D ∧ ‖D‖ ≤ B := by
  have hsfin : (∫⁻ x, localSlope f x ^ 2 ∂m) < ∞ := by
    by_contra hh
    have ht : (∫⁻ x, localSlope f x ^ 2 ∂m) = ∞ := top_le_iff.mp (not_lt.mp hh)
    norm_num [ht] at he
  have hs := memLp_localSlope_of_lintegral_lt_top hf hsfin
  refine ⟨hs.toLp (fun x => (localSlope f x).toReal), ?_, ?_⟩
  · exact (localSlope_isLocalWeakUpperGradient hfinite hf).congr_ae
      hf2.coeFn_toLp.symm hs.coeFn_toLp.symm
  · rw [half_lintegral_localSlope_eq hf hs] at he
    have hsq : ‖hs.toLp (fun x => (localSlope f x).toReal)‖ ^ 2 / 2 ≤ B ^ 2 / 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
    nlinarith [norm_nonneg (hs.toLp (fun x => (localSlope f x).toReal))]

lemma exists_upperGradient_of_cheeger_lt (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : MemLp f 2 m) {B : ℝ} (hB : 0 ≤ B)
    (he : cheegerEnergy m f < ENNReal.ofReal (B ^ 2 / 2)) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B := by
  rw [cheegerEnergy, ite_eq_left hf, sInf_lt_iff] at he
  obtain ⟨a, ⟨fs, hfs, hconv, ha⟩, hab⟩ := he
  let u : ℕ → Lp ℝ 2 m := fun n => (hfs n).2.toLp (fs n)
  have hu : Tendsto u atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs (fun n => (hfs n).2) f hf).mpr hconv
  have hfreq : ∃ᶠ n in atTop, u n ∈ {u : Lp ℝ 2 m | ∃ D : Lp ℝ 2 m,
      IsLocalWeakUpperGradient m u D ∧ ‖D‖ ≤ B} := by
    have H := frequently_lt_of_liminf_lt (f := atTop) (b := ENNReal.ofReal (B ^ 2 / 2)) (u := fun n => (2 : ℝ≥0∞)⁻¹ *
      (∫⁻ x, localSlope (fs n) x ^ 2 ∂m)) (h := by simpa only [← ha] using hab)
    apply H.mono
    intro n hn
    obtain ⟨L, hL⟩ := (hfs n).1
    exact lipschitz_mem_upperGradient_sublevel hfinite hL (hfs n).2 hB hn.le
  obtain ⟨D, hD, hDB⟩ := (isClosed_upperGradient_sublevel (m := m) B).mem_of_frequently_of_tendsto hfreq hu
  exact ⟨D, hD.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, hDB⟩

lemma exists_upperGradient_energy_le_cheeger (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : MemLp f 2 m) (he : cheegerEnergy m f < ∞) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧
      ENNReal.ofReal (‖D‖ ^ 2 / 2) ≤ cheegerEnergy m f := by
  let a := (cheegerEnergy m f).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have haB : a < (a + 2) ^ 2 / 2 := by nlinarith [sq_nonneg a]
  have hE : cheegerEnergy m f < ENNReal.ofReal ((a + 2) ^ 2 / 2) := by
    rw [← ENNReal.ofReal_toReal he.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr haB
  obtain ⟨D₀, hD₀, _⟩ := exists_upperGradient_of_cheeger_lt hfinite hf (by linarith : 0 ≤ a + 2) hE
  obtain ⟨D, hD, hmin⟩ := exists_norm_minimal_upperGradient
    (f := hf.toLp f) ⟨D₀, hD₀.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl⟩
  refine ⟨D, hD.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrt : r = ∞
  · rw [hrt]
    exact le_top
  let B : ℝ := Real.sqrt (2 * r.toReal)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBs : B ^ 2 / 2 = r.toReal := by
    dsimp only [B]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * r.toReal)]
    ring
  have hEB : cheegerEnergy m f < ENNReal.ofReal (B ^ 2 / 2) := by
    rwa [hBs, ENNReal.ofReal_toReal hrt]
  obtain ⟨E, hE, hEn⟩ := exists_upperGradient_of_cheeger_lt hfinite hf hB hEB
  have hDE : ‖D‖ ≤ B :=
    (hmin E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)).trans hEn
  calc
    ENNReal.ofReal (‖D‖ ^ 2 / 2) ≤ ENNReal.ofReal (B ^ 2 / 2) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [norm_nonneg D]
    _ = r := by rw [hBs, ENNReal.ofReal_toReal hrt]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
