import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserTransport
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombInverseFifth

namespace OAI

/-! Uniform integral domination for the actual Moser flow. In particular,
the transported inverse-fifth tail keeps its inverse-square integral bound. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem transportedInverseFifth_integrableOn {H S r : ℝ}
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hr : 0 < r)
    (G : Position → Position) (hG : Continuous G) (y : Position) :
    IntegrableOn (fun x => inverseFifthTail r (y-G x)) (slabDomain H S) := by
  apply IntegrableOn.of_bound (slabDomain_isCompact hH hS).measure_lt_top
    (((inverseFifthTail_measurable r).comp (continuous_const.sub hG).measurable).aestronglyMeasurable.restrict)
    (1/r^5)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖inverseFifthTail r (y-G x)‖ ≤ 1/r^5
    rw [Real.norm_of_nonneg (inverseFifthTail_nonneg _ _)]
    exact inverseFifthTail_le hr _)

theorem moser_nonnegative_integral_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (f : Position → ℝ) (hf : Integrable f) (hpos : ∀ x, 0 ≤ f x) :
    (∫ x in slabDomain H S, f (G x 1)) ≤ (3/2:ℝ)*(∫ x, f x) := by
  have hs := (slabDomain_isClosed H S).measurableSet
  have hb := synthesizedDensity_bounds hrho.le V hsupport hbound
  have hm : Measurable (synthesizedDensity rho H S V) :=
    (measurable_const.indicator hs).add
      (manufacturedCharge_continuous V (hV.of_le (by norm_num))).measurable
  have hi : Integrable (fun x => synthesizedDensity rho H S V x*f x) :=
    hf.bdd_mul (c := 3*rho/2) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hb x).1]; exact (hb x).2))
  have htrans := moser_density_integral hpublished hrho V hV hbound hsupport G hG hbij hfix f
  have he : rho*(∫ x in slabDomain H S, f (G x 1)) ≤ (3*rho/2)*(∫ x, f x) := by
    calc
      _ = ∫ x in slabDomain H S, synthesizedDensity rho H S V x*f x := htrans.symm
      _ ≤ ∫ x in slabDomain H S, (3*rho/2)*f x :=
        setIntegral_mono_on hi.integrableOn (hf.const_mul _).integrableOn hs
          (fun x _ => mul_le_mul_of_nonneg_right (hb x).2 (hpos x))
      _ ≤ ∫ x, (3*rho/2)*f x :=
        setIntegral_le_integral (hf.const_mul _)
          (Filter.Eventually.of_forall (fun x => mul_nonneg (by positivity) (hpos x)))
      _ = _ := integral_const_mul _ _
  apply (mul_le_mul_iff_right₀ hrho).mp
  convert he using 1
  ring

theorem moser_inverseFifth_tail_bound (hpublished : PublishedC4FlowInput)
    {rho H S : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (hsupport : tsupport V ⊆ slabDomain H S)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (hbij : Function.Bijective (fun x => G x 1))
    (hfix : ∀ x, x ∉ tsupport V → G x 1 = x)
    (y : Position) {r : ℝ} (hr : 0 < r) :
    (∫ x in slabDomain H S, inverseFifthTail r (y-G x 1)) ≤ 3*Real.pi/r^2 := by
  have he := moser_nonnegative_integral_bound hpublished hrho V hV hbound hsupport G hG hbij hfix
    (fun x => inverseFifthTail r (y-x)) (translatedInverseFifth_integrable y hr)
    (fun x => inverseFifthTail_nonneg r (y-x))
  rw [translatedInverseFifth_integral y hr] at he
  convert he using 1
  ring

end ContinuumCoulomb

end

end OAI
