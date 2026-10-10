import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoreScreenedField
import OAI.Analysis.CoulombRadii.FormDomain.SchwartzSquareIntegrable

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma packetDensity_ofReal (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    ENNReal.ofReal (packetDensity g ρ x) = ∫⁻ y : Space, ENNReal.ofReal (g (x-y)^2*ρ y) :=
  ofReal_integral_eq_lintegral_ofReal (packetDensity_integrand_integrable g ρ hp hm hi x)
    (Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (hp y)))

lemma packetDensity_product_ofReal (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) (x y : Space) :
    ENNReal.ofReal (packetDensity g ρ x*packetDensity g ρ y) =
      ∫⁻ ac : Space × Space, ENNReal.ofReal (g (x-ac.1)^2*g (y-ac.2)^2) *
        ENNReal.ofReal (ρ ac.1*ρ ac.2) := by
  rw [ENNReal.ofReal_mul (packetDensity_nonneg g ρ hp x),packetDensity_ofReal g ρ hp hm hi x,
    packetDensity_ofReal g ρ hp hm hi y]
  have hx : Measurable (fun a : Space => ENNReal.ofReal (g (x-a)^2*ρ a)) :=
    (((g.continuous.measurable.comp (measurable_const.sub measurable_id)).pow_const 2).mul hm).ennreal_ofReal
  have hy : Measurable (fun c : Space => ENNReal.ofReal (g (y-c)^2*ρ c)) :=
    (((g.continuous.measurable.comp (measurable_const.sub measurable_id)).pow_const 2).mul hm).ennreal_ofReal
  rw [← lintegral_prod_mul hx.aemeasurable hy.aemeasurable]
  apply lintegral_congr
  intro ac
  simp only [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_mul (hp _)]
  ring

lemma packetDensity_pair_lintegral (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ) :
    ENNReal.ofReal (∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
      (packetDensity g ρ xy.1*packetDensity g ρ xy.2)) =
    ∫⁻ ac : Space × Space, ENNReal.ofReal (ρ ac.1*ρ ac.2)*
      ENNReal.ofReal (∫ xy : Space × Space,
        g (xy.1-ac.1)^2*g (xy.2-ac.2)^2*coulombKernel (xy.1-xy.2)) := by
  let H (xy ac : Space × Space) : ℝ≥0∞ := ENNReal.ofReal (g (xy.1-ac.1)^2*g (xy.2-ac.2)^2)*
    ENNReal.ofReal (ρ ac.1*ρ ac.2)*ENNReal.ofReal (coulombKernel (xy.1-xy.2))
  have hH : Measurable (Function.uncurry H) := by
    unfold H Function.uncurry
    exact (((((g.continuous.measurable.comp (measurable_fst.fst.sub measurable_snd.fst)).pow_const 2).mul
      ((g.continuous.measurable.comp (measurable_fst.snd.sub measurable_snd.snd)).pow_const 2)).ennreal_ofReal).mul
      (((hm.comp measurable_snd.fst).mul (hm.comp measurable_snd.snd)).ennreal_ofReal)).mul
      ((coulombKernel_measurable.comp (measurable_fst.fst.sub measurable_fst.snd)).ennreal_ofReal)
  have he (ac : Space × Space) : (∫⁻ xy : Space × Space, H xy ac) =
      ENNReal.ofReal (ρ ac.1*ρ ac.2)*ENNReal.ofReal (∫ xy : Space × Space,
        g (xy.1-ac.1)^2*g (xy.2-ac.2)^2*coulombKernel (xy.1-xy.2)) := by
    have hm' (a : Space) : Measurable (fun x : Space => g (x-a)^2) :=
      (g.continuous.measurable.comp (measurable_id.sub measurable_const)).pow_const 2
    have hb (c x : Space) : ‖g (x-c)^2‖ ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 := by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact schwartz_square_le g _
    have hij := coulomb_pair_integrable (window_shift_integrable g ac.1) (hm' ac.1)
      (window_shift_integrable g ac.2) (hm' ac.2) (hb ac.2)
    rw [ofReal_integral_eq_lintegral_ofReal hij (Eventually.of_forall (fun xy =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (coulombKernel_nonneg _)))]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro xy
    dsimp only [H]
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    ac_rfl
  have hI := ofReal_integral_eq_lintegral_ofReal (packetDensity_pair_integrable g ρ hp hm hi)
    (Eventually.of_forall (fun xy => mul_nonneg (coulombKernel_nonneg _)
      (mul_nonneg (packetDensity_nonneg g ρ hp _) (packetDensity_nonneg g ρ hp _))))
  rw [hI]
  calc
    _ = ∫⁻ xy : Space × Space, ∫⁻ ac : Space × Space, H xy ac := by
      apply lintegral_congr
      intro xy
      rw [ENNReal.ofReal_mul (coulombKernel_nonneg _),packetDensity_product_ofReal g ρ hp hm hi]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro ac
      dsimp only [H]
      ac_rfl
    _ = ∫⁻ ac : Space × Space, ∫⁻ xy : Space × Space, H xy ac :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = _ := lintegral_congr he

lemma radial_packetDensity_pair_le (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hi : Integrable ρ)
    (hD : Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2))) :
    (∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(packetDensity g ρ xy.1*packetDensity g ρ xy.2)) ≤
      ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2) := by
  have hpos : 0 ≤ ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2) :=
    integral_nonneg (fun xy => mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hp _) (hp _)))
  apply (ENNReal.ofReal_le_ofReal_iff hpos).mp
  rw [packetDensity_pair_lintegral g ρ hp hm hi,
    ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall (fun xy =>
      mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hp _) (hp _))))]
  apply lintegral_mono_ae
  have hne : ∀ᵐ ac : Space × Space ∂(volume : Measure Space).prod volume, ac.1 ≠ ac.2 := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun ac : Space × Space => ac.1 ≠ ac.2)
      ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).mpr
    filter_upwards [] with a
    have h : ∀ᵐ c : Space, c ≠ a := by rw [ae_iff]; simp
    exact h.mono (fun c hc => Ne.symm hc)
  filter_upwards [hne] with ac hac
  rw [ENNReal.ofReal_mul (coulombKernel_nonneg _),mul_comm (ENNReal.ofReal (coulombKernel _))]
  gcongr
  exact window_shape_pair_le g hg hrad hac
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
