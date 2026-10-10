import Mathlib

namespace OAI

/-!
# Scalar Laplace profile estimates

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

namespace CriticalHoneycomb.RenewalInput
open MeasureTheory Set Filter

/-- Scalar comparison used in the actual bridge renewal transform. -/
noncomputable def laplaceProfile (s x : ℝ) : ℝ :=
  Real.exp (-(s*x)) * (1+x)^(-(1:ℝ)/4)

lemma laplaceProfile_pos {x : ℝ} (hx : 0 ≤ x) (s : ℝ) : 0<laplaceProfile s x := by
  unfold laplaceProfile
  positivity

lemma laplaceProfile_antitone {s : ℝ} (hs : 0 ≤ s) :
    AntitoneOn (laplaceProfile s) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith))
    (Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+x) (by linarith) (by norm_num))
    (by positivity) (Real.exp_pos _).le

lemma laplaceProfile_continuous (s : ℝ) : ContinuousOn (laplaceProfile s) (Ici 0) := by
  apply ContinuousOn.mul (by fun_prop)
  exact (continuousOn_const.add continuousOn_id).rpow_const (fun x hx ↦ Or.inl (by have : 0 ≤ x := hx; linarith : 1+x ≠ 0))

lemma gammaProfile_integral {s : ℝ} (hs : 0<s) :
    ∫ x in Ioi (0:ℝ), Real.exp (-(s*x))*x^(-(1:ℝ)/4) =
      s^(-(3:ℝ)/4)*Real.Gamma (3/4) := by
  have h:=Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : 0<(3:ℝ)/4) hs
  convert h using 1
  · congr 1; funext x; norm_num; ring
  · rw [one_div,Real.inv_rpow hs.le,←Real.rpow_neg hs.le]
    norm_num

lemma gammaProfile_integrable {s : ℝ} (hs : 0<s) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-(s*x))*x^(-(1:ℝ)/4)) (Ioi 0) := by
  by_contra h
  have hz:=integral_undef h
  rw [gammaProfile_integral hs] at hz
  have hp : 0<s^(-(3:ℝ)/4)*Real.Gamma (3/4) := by positivity
  linarith

lemma laplaceProfile_integrable {s : ℝ} (hs : 0<s) :
    IntegrableOn (laplaceProfile s) (Ioi 0) := by
  refine (gammaProfile_integrable hs).mono' ((laplaceProfile_continuous s).mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (laplaceProfile_pos hx.le s).le]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx (by linarith : x ≤ 1+x) (by norm_num)) (Real.exp_pos _).le

lemma laplaceProfile_summable {s : ℝ} (hs : 0<s) :
    Summable (fun n : ℕ ↦ laplaceProfile s n) :=
  (laplaceProfile_antitone hs.le).summable_of_integrableOn_Ioi_zero
    (laplaceProfile_integrable hs) (fun _ hx ↦ (laplaceProfile_pos hx.le s).le)

lemma laplaceProfile_integral_le {s : ℝ} (hs : 0<s) :
    ∫ x in Ioi (0:ℝ), laplaceProfile s x  ≤  s^(-(3:ℝ)/4)*Real.Gamma (3/4) := by
  rw [←gammaProfile_integral hs]
  refine integral_mono_ae (laplaceProfile_integrable hs) (gammaProfile_integrable hs) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx (by linarith : x ≤ 1+x) (by norm_num)) (Real.exp_pos _).le

lemma laplaceProfile_sum_upper {s : ℝ} (hs : 0<s) (hs1 : s ≤ 1) :
    ∑' n : ℕ, laplaceProfile s n  ≤  (1+Real.Gamma (3/4))*s^(-(3:ℝ)/4) := by
  have h:=(laplaceProfile_antitone hs.le).tsum_le_integral
    (laplaceProfile_integrable hs) (fun _ hx ↦ (laplaceProfile_pos hx.le s).le)
  have hone : 1 ≤ s^(-(3:ℝ)/4) := by
    simpa using Real.rpow_le_rpow_of_nonpos hs hs1 (by norm_num : -(3:ℝ)/4 ≤ 0)
  have hi:=laplaceProfile_integral_le hs
  simp only [show laplaceProfile s 0=1 by simp [laplaceProfile]] at h
  nlinarith

lemma laplaceProfile_sum_lower {s : ℝ} (hs : 0<s) (hs1 : s ≤ 1) :
    Real.exp (-1)*(2:ℝ)^(-(1:ℝ)/4)*s^(-(3:ℝ)/4)  ≤ 
      ∑' n : ℕ, laplaceProfile s n := by
  have hi:=laplaceProfile_integrable hs
  have hnn : 0  ≤ᵐ[volume.restrict (Ioi (0:ℝ))] laplaceProfile s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (laplaceProfile_pos hx.le s).le
  have hsub : Ioc (0:ℝ) (1/s) ⊆ Ioi 0 := fun x hx ↦ hx.1
  have hfinite:=setIntegral_mono_set hi hnn (Filter.Eventually.of_forall hsub)
  have hlo : ∫ x in Ioc (0:ℝ) (1/s), Real.exp (-1)*(2/s)^(-(1:ℝ)/4)  ≤ 
      ∫ x in Ioc (0:ℝ) (1/s), laplaceProfile s x := by
    refine integral_mono_ae (integrableOn_const (C := Real.exp (-1)*(2/s)^(-(1:ℝ)/4)) (by simp [Real.volume_Ioc])) (hi.mono_set hsub) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0<x := hx.1
    have hx1 : x ≤ 1/s := hx.2
    have hxs : s*x ≤ 1 := by have h:=(le_div_iff₀ hs).mp hx.2; nlinarith
    have hbase : 1+x ≤ 2/s := by
      have h1 : 1 ≤ 1/s := (le_div_iff₀ hs).mpr (by linarith)
      have he : 2/s=(1/s:ℝ)+(1/s) := by ring
      rw [he]; linarith
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
      (Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+x) hbase (by norm_num))
      (by positivity) (Real.exp_pos _).le
  have hconst : ∫ x in Ioc (0:ℝ) (1/s), Real.exp (-1)*(2/s)^(-(1:ℝ)/4) =
      Real.exp (-1)*(2:ℝ)^(-(1:ℝ)/4)*s^(-(3:ℝ)/4) := by
    rw [setIntegral_const]
    simp only [Measure.real,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/s),smul_eq_mul]
    rw [show (2/s:ℝ)=2*s⁻¹ by ring,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (inv_nonneg.mpr hs.le)]
    rw [one_div,Real.inv_rpow hs.le,←Real.rpow_neg hs.le]
    rw [←Real.rpow_neg_one s]
    calc
      _ = Real.exp (-1)*(2:ℝ)^(-(1:ℝ)/4)*(s^(-1:ℝ)*s^(-(-(1:ℝ)/4))) := by ring
      _ = _ := by rw [←Real.rpow_add hs]; norm_num
  rw [hconst] at hlo
  exact (hlo.trans hfinite).trans ((laplaceProfile_antitone hs.le).integral_le_tsum
    (laplaceProfile_summable hs) (fun _ hx ↦ (laplaceProfile_pos hx.le s).le))

end CriticalHoneycomb.RenewalInput

end

end OAI
