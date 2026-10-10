import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserIntegralBound

namespace OAI

/-! Integrability across the transported Coulomb pole follows from the
actual Jacobian identity, including a uniform lower bound on the Jacobian. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem moser_flowJacobian_lower (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (2/3:ℝ) ≤ flowJacobian G t x := by
  have he := moser_density_jacobian hpublished hrho V hV hbound G hG x ht
  have hp := moser_flowJacobian_pos hpublished hrho V hV hbound G hG x ht
  have hb := (homotopyDensity_bounds V hbound ht.1 ht.2 (G x t)).2
  have hm := mul_le_mul_of_nonneg_right hb hp.le
  nlinarith

theorem moser_integrableOn_comp (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (f : Position → ℝ) (hf : Measurable f) (hi : IntegrableOn f (slabDomain H S)) :
    IntegrableOn (fun x => f (G x 1)) (slabDomain H S) := by
  have h1 : (1:ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num,le_rfl⟩
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 h1
  have himage := moser_time_one_preserves_slab V hsupport (fun x => G x 1) hbij hfix
  have he := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := volume) (slabDomain_isClosed H S).measurableSet
    (fun x (_hx : x ∈ slabDomain H S) =>
      (hreg.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
    hbij.1.injOn f
  rw [himage] at he
  have hw := he.mp hi
  apply (hw.norm.const_mul (3/2:ℝ)).mono'
    ((hf.comp hreg.continuous.measurable).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖f (G x 1)‖ ≤ (3/2:ℝ)*‖|flowJacobian G 1 x| • f (G x 1)‖
    rw [norm_smul,Real.norm_of_nonneg (abs_nonneg _),
      abs_of_pos (moser_flowJacobian_pos hpublished hrho V hV hbound G hG x h1)]
    have hb := moser_flowJacobian_lower hpublished hrho V hV hbound G hG x h1
    nlinarith [norm_nonneg (f (G x 1))])

theorem moser_truncatedCoulomb_integrable (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) (r : ℝ) :
    IntegrableOn (fun x => Coulomb.truncatedCoulomb r (y-G x 1)) (slabDomain H S) := by
  apply moser_integrableOn_comp hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.truncatedCoulomb r (y-x))
  · exact ((Coulomb.coulombKernel_measurable.indicator measurableSet_ball).comp
      (continuous_const.sub continuous_id).measurable)
  · exact ((Coulomb.truncatedCoulomb_integrable r).comp_sub_left y).integrableOn

theorem moser_truncatedCoulomb_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in slabDomain H S, Coulomb.truncatedCoulomb r (y-G x 1)) ≤ 3*Real.pi*r^2 := by
  have he := moser_nonnegative_integral_bound hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => Coulomb.truncatedCoulomb r (y-x))
    ((Coulomb.truncatedCoulomb_integrable r).comp_sub_left y)
    (fun x => Coulomb.truncatedCoulomb_nonneg r (y-x))
  rw [integral_sub_left_eq_self,Coulomb.truncatedCoulomb_integral hr] at he
  convert he using 1
  ring

theorem moser_coulomb_integrableOn (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x) (y : Position) :
    IntegrableOn (fun x => Coulomb.coulombKernel (y-G x 1)) (slabDomain H S) := by
  have ht := moser_truncatedCoulomb_integrable hpublished hrho V hV hbound hsupport
    G hG hbij hfix y 1
  have hc : IntegrableOn (fun _ : Position => (1:ℝ)) (slabDomain H S) :=
    integrableOn_const ((slabDomain_isCompact hH hS).measure_lt_top (μ := volume)).ne
  have hreg := (moser_flow_C4 hpublished hrho V hV hbound G hG).1 1 ⟨by norm_num,le_rfl⟩
  apply (ht.add hc).mono'
    ((Coulomb.coulombKernel_measurable.comp
      (continuous_const.sub hreg.continuous).measurable).aestronglyMeasurable.restrict)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖Coulomb.coulombKernel (y-G x 1)‖ ≤ Coulomb.truncatedCoulomb 1 (y-G x 1)+1
    rw [Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
    simpa only [one_mul,mul_one,inv_one] using
      Coulomb.coulomb_integrand_bound (f := fun _ => (1:ℝ))
        (fun _ => zero_le_one) (fun _ => le_rfl) (by norm_num : (0:ℝ) < 1) y (G x 1))

end ContinuumCoulomb

end

end OAI
