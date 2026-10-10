import Mathlib
import OAI.Analysis.HardSphere.Model

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace HardSphere.Phase

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

def HasCommonPhase (f : X → ℂ) (U : Set X) (ν : Measure X) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ᵐ x ∂ν.restrict U, f x = c * (‖f x‖ : ℂ)

lemma norm_setIntegral_of_commonPhase {f : X → ℂ} {U : Set X}
    (hphase : HasCommonPhase f U ν) :
    ‖∫ x in U, f x ∂ν‖ = ∫ x in U, ‖f x‖ ∂ν := by
  obtain ⟨c, hc, heq⟩ := hphase
  rw [integral_congr_ae heq, integral_const_mul, integral_complex_ofReal, norm_mul,
    hc, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]

lemma slice_phase_loss {f : X → ℂ} (hf : Integrable f ν) {U : Set X}
    (hU : MeasurableSet U) (hphase : HasCommonPhase f U ν) :
    (∫ x, ‖f x‖ ∂ν)^2 - ‖∫ x, f x ∂ν‖^2 ≤
      4 * (∫ x, ‖f x‖ ∂ν) * (∫ x in Uᶜ, ‖f x‖ ∂ν) := by
  have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hb : 0 ≤ ∫ x in Uᶜ, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hn : ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν := norm_integral_le_integral_norm _
  have htri := norm_sub_le (∫ x, f x ∂ν) (∫ x in Uᶜ, f x ∂ν)
  have hdecomp := integral_add_compl hU hf
  have hdecompNorm := integral_add_compl hU hf.norm
  have hdiff : (∫ x, f x ∂ν) - (∫ x in Uᶜ, f x ∂ν) = ∫ x in U, f x ∂ν := by
    rw [← hdecomp]; abel
  rw [hdiff, norm_setIntegral_of_commonPhase hphase] at htri
  have hsmall := norm_integral_le_integral_norm (μ := ν.restrict Uᶜ) f
  have he : (∫ x, ‖f x‖ ∂ν) - ‖∫ x, f x ∂ν‖ ≤
      2 * (∫ x in Uᶜ, ‖f x‖ ∂ν) := by linarith
  have he' : (∫ x, ‖f x‖ ∂ν) + ‖∫ x, f x ∂ν‖ ≤ 2 * (∫ x, ‖f x‖ ∂ν) := by linarith
  have hprod := mul_le_mul he he' (by positivity) (by positivity :
    0 ≤ 2 * (∫ x in Uᶜ, ‖f x‖ ∂ν))
  nlinarith [hprod]

lemma integral_mul_le_sqrt (f g : X → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    ∫ x, f x * g x ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) *
      Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

lemma integral_norm_sq_le [IsFiniteMeasure ν] {f : X → ℂ} (hf : MemLp f 2 ν) :
    (∫ x, ‖f x‖ ∂ν)^2 ≤ ν.real univ * ∫ x, ‖f x‖ ^ 2 ∂ν := by
  have h := integral_mul_le_sqrt (fun _ : X ↦ 1) (fun x ↦ ‖f x‖)
    (memLp_const 1) hf.norm (Eventually.of_forall fun _ ↦ zero_le_one)
    (Eventually.of_forall fun _ ↦ norm_nonneg _)
  simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] at h
  have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hm : 0 ≤ ∫ x, ‖f x‖^2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  have hs := (sq_le_sq₀ ha (by positivity)).2 h
  simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg), Real.sq_sqrt hm] using hs

end HardSphere.Phase

namespace HardSphere.Phase

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ]

lemma memLp_slices {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, MemLp (fun x ↦ f (y,x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

lemma memLp_integral_norm {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν) 2 μ := by
  have hm := hf.aestronglyMeasurable.norm.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).2
  have hi := (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
  apply (hi.const_mul (ν.real univ)).mono' (hm.pow 2)
  filter_upwards [memLp_slices hf] with y hy
  change ‖(∫ x, ‖f (y,x)‖ ∂ν)^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact integral_norm_sq_le hy

lemma setIntegral_norm_sq_le {f : X → ℂ} (hf : MemLp f 2 ν) (A : Set X) :
    (∫ x in A, ‖f x‖ ∂ν)^2 ≤ ν.real A * ∫ x, ‖f x‖^2 ∂ν := by
  have h := integral_norm_sq_le (hf.restrict (s := A))
  simp only [Measure.real, Measure.restrict_apply_univ] at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun _ ↦ sq_nonneg _)
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

def occupation (f : Y × X → ℂ) (μ : Measure Y) (ν : Measure X) : ℝ :=
  (∫ y, ‖∫ x, f (y,x) ∂ν‖^2 ∂μ) / ν.real univ

def modulusOccupation (f : Y × X → ℂ) (μ : Measure Y) (ν : Measure X) : ℝ :=
  (∫ y, (∫ x, ‖f (y,x)‖ ∂ν)^2 ∂μ) / ν.real univ

def geometricLoss (f : Y × X → ℂ) (U : Set (Y × X))
    (μ : Measure Y) (ν : Measure X) : ℝ :=
  (∫ y, ν.real (Prod.mk y ⁻¹' Uᶜ) * (∫ x, ‖f (y,x)‖^2 ∂ν) ∂μ) / ν.real univ

theorem phase_transfer {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν))
    (hnorm : ∫ z, ‖f z‖^2 ∂μ.prod ν = 1) (hV : 0 < ν.real univ)
    {U : Set (Y × X)} (hU : MeasurableSet U)
    (hphase : ∀ᵐ y ∂μ, HasCommonPhase (fun x ↦ f (y,x)) (Prod.mk y ⁻¹' U) ν) :
    modulusOccupation f μ ν - 4 * Real.sqrt (geometricLoss f U μ ν) ≤
      occupation f μ ν := by
  let a : Y → ℝ := fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν
  let b : Y → ℝ := fun y ↦ ∫ x in Prod.mk y ⁻¹' Uᶜ, ‖f (y,x)‖ ∂ν
  let c : Y → ℝ := fun y ↦ ‖∫ x, f (y,x) ∂ν‖
  let m : Y → ℝ := fun y ↦ ∫ x, ‖f (y,x)‖^2 ∂ν
  let v : Y → ℝ := fun y ↦ ν.real (Prod.mk y ⁻¹' Uᶜ)
  let V : ℝ := ν.real univ
  have ha0 (y) : 0 ≤ a y := integral_nonneg fun _ ↦ norm_nonneg _
  have hb0 (y) : 0 ≤ b y := integral_nonneg fun _ ↦ norm_nonneg _
  have hc0 (y) : 0 ≤ c y := norm_nonneg _
  have hm0 (y) : 0 ≤ m y := integral_nonneg fun _ ↦ sq_nonneg _
  have hv0 (y) : 0 ≤ v y := measureReal_nonneg
  have hvV (y) : v y ≤ V := measureReal_mono (by simp)
  have ha : MemLp a 2 μ := memLp_integral_norm hf
  have hbmeas : AEStronglyMeasurable b μ := by
    have h := (hf.aestronglyMeasurable.norm.indicator hU.compl).integral_prod_right'
    convert h using 1
    ext y
    dsimp only [b]
    rw [← integral_indicator (hU.compl.preimage measurable_prodMk_left)]
    rfl
  have hb : MemLp b 2 μ := by
    apply ha.mono' hbmeas
    filter_upwards [memLp_slices hf] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 y)]
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (hy.integrable (by norm_num)).norm
  have hc : MemLp c 2 μ := by
    refine ha.mono' hf.aestronglyMeasurable.integral_prod_right'.norm ?_
    exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hc0 y)]
      exact norm_integral_le_integral_norm _
  have hmi : Integrable m μ :=
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
  have hvmeas : Measurable v := (measurable_measure_prodMk_left hU.compl).ennreal_toReal
  have hvmi : Integrable (fun y ↦ v y * m y) μ := by
    refine (hmi.const_mul V).mono' (hvmeas.aestronglyMeasurable.mul hmi.aestronglyMeasurable) ?_
    exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hv0 y) (hm0 y))]
      exact mul_le_mul_of_nonneg_right (hvV y) (hm0 y)
  have hmass : ∫ y, m y ∂μ = 1 := by
    rw [← integral_prod _ (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
    exact hnorm
  have ha2 : ∫ y, a y ^ 2 ∂μ ≤ V := by
    calc
      _ ≤ ∫ y, V * m y ∂μ := by
        apply integral_mono_ae ha.integrable_sq (hmi.const_mul V)
        filter_upwards [memLp_slices hf] with y hy
        exact integral_norm_sq_le hy
      _ = V := by rw [integral_const_mul, hmass, mul_one]
  have hb2 : ∫ y, b y ^ 2 ∂μ ≤ ∫ y, v y * m y ∂μ := by
    apply integral_mono_ae hb.integrable_sq hvmi
    filter_upwards [memLp_slices hf] with y hy
    exact setIntegral_norm_sq_le hy _
  have hmul : ∫ y, a y * b y ∂μ ≤
      Real.sqrt V * Real.sqrt (∫ y, v y * m y ∂μ) := by
    refine (integral_mul_le_sqrt a b ha hb
      (Eventually.of_forall ha0) (Eventually.of_forall hb0)).trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt ha2) (Real.sqrt_le_sqrt hb2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hab : Integrable (fun y ↦ a y * b y) μ := ha.integrable_mul hb
  have hloss : (∫ y, a y^2 ∂μ) - (∫ y, c y^2 ∂μ) ≤
      4 * ∫ y, a y * b y ∂μ := by
    rw [← integral_sub ha.integrable_sq hc.integrable_sq, ← integral_const_mul]
    apply integral_mono_ae (ha.integrable_sq.sub hc.integrable_sq) (hab.const_mul 4)
    filter_upwards [memLp_slices hf, hphase] with y hy hp
    simpa only [a, b, c, Pi.sub_apply, preimage_compl, mul_assoc] using
      slice_phase_loss (hy.integrable (by norm_num))
        (hU.preimage measurable_prodMk_left) hp
  have hd0 : 0 ≤ ∫ y, v y * m y ∂μ := integral_nonneg fun y ↦ mul_nonneg (hv0 y) (hm0 y)
  have hroot : Real.sqrt V * Real.sqrt (∫ y, v y * m y ∂μ) =
      V * Real.sqrt ((∫ y, v y * m y ∂μ) / V) := by
    rw [Real.sqrt_div hd0, ← mul_div_assoc]
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 hV))).2
    calc
      _ = (Real.sqrt V * Real.sqrt V) * Real.sqrt (∫ y, v y * m y ∂μ) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hV.le]
  have h : (∫ y, a y^2 ∂μ) - (∫ y, c y^2 ∂μ) ≤
      4 * V * Real.sqrt ((∫ y, v y * m y ∂μ) / V) := by
    calc
      _ ≤ 4 * ∫ y, a y * b y ∂μ := hloss
      _ ≤ 4 * (Real.sqrt V * Real.sqrt (∫ y, v y * m y ∂μ)) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by rw [hroot]; ring
  dsimp only [modulusOccupation, occupation, geometricLoss]
  change (∫ y, a y^2 ∂μ) / V - 4 * Real.sqrt ((∫ y, v y * m y ∂μ) / V) ≤
    (∫ y, c y^2 ∂μ) / V
  apply (le_div_iff₀ (show 0 < V from hV)).2
  have hvne : V ≠ 0 := ne_of_gt hV
  rw [sub_mul, div_mul_cancel₀ _ hvne]
  nlinarith

end HardSphere.Phase

end
end

end

end OAI
