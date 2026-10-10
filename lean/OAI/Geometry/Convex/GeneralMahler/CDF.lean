import OAI.Geometry.Convex.GeneralMahler.Density

namespace OAI
/-! One-dimensional Gaussian layers, preliminary identities and bounds (§§01--02). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Real Metric Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal
namespace GeneralMahler
namespace Layers

def p (z : ℝ) := ∫ x in Iic z, phi x
def a (z : ℝ) := phi z + z*p z

lemma d_phi (z : ℝ) : HasDerivAt phi (-z*phi z) z := by
  simp_rw [funext phi_apply]
  have he := ((hasDerivAt_id' z).pow 2).neg.div_const 2
  convert he.exp.const_mul (√(2 * π))⁻¹ using 1
  all_goals first | rfl | (simp; ring)

lemma c_phi : Continuous phi :=
  continuous_iff_continuousAt.mpr fun x => (d_phi x).continuousAt
lemma i_phi : Integrable phi := integrable_gaussianPDFReal _ _
lemma e_phi : ∫ x, phi x = 1 := integral_gaussianPDFReal_eq_one _ one_ne_zero

lemma int_Ioi (z : ℝ) : ∫ x in Ioi z, phi x = 1-p z := by
  have h := integral_add_compl measurableSet_Iic (μ := volume) i_phi (s := Iic z)
  rw [compl_Iic,e_phi] at h
  dsimp [p]
  linarith

lemma neg_phi (x : ℝ) : phi (-x) = phi x := by simp [phi_apply]

lemma neg_p (z : ℝ) : p (-z) = 1-p z := by
  rw [← int_Ioi, ← integral_Ici_eq_integral_Ioi]
  unfold p
  let e := (Homeomorph.neg ℝ).toMeasurableEquiv
  have he := setIntegral_map_equiv (μ := volume) e phi (Iic (-z))
  have hm : Measure.map e volume = volume := measurePreserving_neg _ |>.map_eq
  rw [hm] at he
  rw [he]
  have he' : e ⁻¹' Iic (-z) = Ici z := by ext; change (-_ ≤ -z) ↔ _; simp
  rw [he']
  exact integral_congr_ae (ae_of_all _ fun x => neg_phi x)

lemma p_half : p 0 = 1/2 := by
  have he := neg_p 0
  rw [neg_zero] at he; linarith

lemma d_p (z : ℝ) : HasDerivAt p (phi z) z := by
  have H : p = fun x => p 0 + ∫ t in (0:ℝ)..x, phi t := by
    ext x
    rw [p,p, ← intervalIntegral.integral_Iic_sub_Iic i_phi.integrableOn i_phi.integrableOn]
    ring
  rw [H]
  exact ((intervalIntegral.integral_hasDerivAt_right (c_phi.intervalIntegrable ..)
    (c_phi.stronglyMeasurableAtFilter _ _) c_phi.continuousAt).const_add _)

lemma d_a (z : ℝ) : HasDerivAt a (p z) z := by
  have he := (d_phi z).add ((hasDerivAt_id' z).mul (d_p z))
  convert he using 1
  all_goals first | rfl | simp

lemma cp : Continuous p := continuous_iff_continuousAt.mpr fun x => (d_p x).continuousAt
lemma ca : Continuous a := continuous_iff_continuousAt.mpr fun x => (d_a x).continuousAt
lemma p_pos (z : ℝ) : 0 < p z := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun x => (phi_pos _).le) i_phi.integrableOn).mpr
  apply lt_of_lt_of_le (isOpen_Iio.measure_pos volume (Set.nonempty_Iio (a := z)))
  apply measure_mono
  exact fun x hx => ⟨(phi_pos x).ne',show x ≤ z from le_of_lt hx⟩

lemma p_lt_one (z : ℝ) : p z < 1 := by
  have h := p_pos (-z)
  rw [neg_p] at h; linarith

lemma p_mono : StrictMono p := strictMono_of_deriv_pos fun z => by
  rw [(d_p _).deriv]; apply p_pos_phi
where p_pos_phi := phi_pos
lemma a_mono : StrictMono a := strictMono_of_deriv_pos fun z => by
  rw [(d_a _).deriv]; apply p_pos

lemma phi_bdd (z : ℝ) : phi z ≤ (√(2*π))⁻¹ := by
  rw [phi_apply]
  apply mul_le_of_le_one_right (by positivity)
  exact exp_le_one_iff.mpr (by nlinarith)

lemma int_moment1 : Integrable (fun z => z * phi z) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul (√(2*π))⁻¹
  convert h using 1
  ext x
  rw [phi_apply]
  ring_nf

lemma moment1 (z : ℝ) : ∫ x in Iic z, -(x * phi x) = phi z := by
  have hlim : Tendsto phi atBot (𝓝 0) := by
    rw [funext phi_apply]
    have he : Tendsto (fun x:ℝ => -(x ^ 2)/2) atBot atBot := by
      refine tendsto_atBot.mpr fun a => ?_
      filter_upwards [eventually_le_atBot (-|2*a|-1)] with x hx
      nlinarith [neg_abs_le (2*a), abs_nonneg (2*a)]
    convert (Real.tendsto_exp_atBot.comp he).const_mul ((√(2*π))⁻¹) using 1 <;> simp
  refine Eq.trans (integral_Iic_of_hasDerivAt_of_tendsto' ?_ int_moment1.neg.integrableOn hlim) (sub_zero _)
  exact fun x hx => by simpa using d_phi x

lemma int_gap (z:ℝ) : Integrable (fun x => (z-x)*phi x) := by
  simp_rw [sub_mul]
  exact (i_phi.const_mul z).sub int_moment1

lemma a_eq (z : ℝ) : a z = ∫ x in Iic z, (z-x)*phi x := by
  simp_rw [sub_mul]
  rw [integral_sub (i_phi.const_mul _).integrableOn int_moment1.integrableOn, integral_const_mul]
  have hh := moment1 z
  rw [integral_neg] at hh
  dsimp [a,p]; rw [← hh]; ring

lemma a_pos (z : ℝ) : 0 < a z := by
  rw [a_eq]
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (int_gap z).integrableOn).mpr
  · apply lt_of_lt_of_le (isOpen_Iio.measure_pos volume (Set.nonempty_Iio (a := z)))
    apply measure_mono
    intro x hx
    exact ⟨ne_of_gt (mul_pos (sub_pos.mpr hx) (phi_pos x)),show x ≤ z from le_of_lt hx⟩
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  exact mul_nonneg (sub_nonneg.mpr hx) (phi_pos x).le

-- Two-sided estimates, exact constants unimportant here.
lemma a_high (s : ℝ) (hs : 0 ≤ s) : a (-s) ≤ phi s := by
  rw [a, neg_phi]
  have h := p_pos (-s); nlinarith

lemma a_low (s : ℝ) (hs : 0 ≤ s) :
    phi s * exp (-4) / (1+s)^2 ≤ a (-s) := by
  let b : ℝ := (1+s)⁻¹
  have hp : 0 < 1+s := by linarith
  have hb : 0 < b := inv_pos.mpr hp
  have hbr : b * (1+s) = 1 := inv_mul_cancel₀ hp.ne'
  have hbs : b*s ≤ 1 := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  let S := Ioc (-s-2*b) (-s-b)
  have hm : MeasurableSet S := measurableSet_Ioc
  have hsub : S ⊆ Iic (-s) := fun x hx => by
    change x ≤ -s; exact hx.2.trans (by linarith)
  have hlow (x) (hx : x ∈ S) : phi s*exp (-4)*b ≤ (-s-x)*phi x := by
    have hh : -s-2*b < x ∧ x ≤ -s-b := hx
    have heQ : x ^ 2 ≤ s ^ 2 + 8 := by
      have h1 : x ^ 2 ≤ (-s-2*b)^2 := by nlinarith
      nlinarith
    have hf : phi s * exp (-4) ≤ phi x := by
      rw [phi_apply,phi_apply,mul_assoc,← Real.exp_add]
      gcongr
      linarith
    rw [mul_comm _ (phi x)]
    exact mul_le_mul hf (by linarith) hb.le (phi_pos x).le
  calc
    _ = ∫ x in S, phi s*exp (-4)*b := by
      rw [setIntegral_const]
      have he : volume.real S = b := by
        rw [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal]
        · ring
        linarith
      rw [he,smul_eq_mul]
      dsimp [b]; field_simp
    _ ≤ ∫ x in S, (-s-x)*phi x := setIntegral_mono_on
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)) ((int_gap _).integrableOn) hm hlow
    _ ≤ a (-s) := by
      rw [a_eq]
      apply setIntegral_mono_set (int_gap _).integrableOn _ (Filter.Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact mul_nonneg (sub_nonneg.mpr hx) (phi_pos _).le

end Layers
end GeneralMahler

end

end OAI
