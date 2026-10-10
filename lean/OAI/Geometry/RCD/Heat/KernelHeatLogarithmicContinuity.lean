import OAI.Geometry.RCD.Heat.KernelHeatContinuityEquation
import OAI.Geometry.RCD.Coordinates.BoundedHeatLogRegular
import OAI.Geometry.RCD.Heat.LocalLogarithmicDifferenceFlux

namespace OAI

/-! # The actual heat bridge continuity equation in logarithmic directions

Compactly supported bounded Sobolev tests see the gradient of the difference
of the two local heat logarithms. The global sources are the actual heat
generators; no continuity-equation hypothesis is supplied.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem kernelHeat_logarithmic_continuity
    (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    {T t : ℝ} (ht : 0 < t) (htT : t < T) {Ω : Set X} (hΩ : IsCompact Ω)
    (hpf : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x)
    (hpg : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) (T-t) g x) :
    let m := hausdorff n X
    let q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    ∃ U V : SobolevSpace m q,
      (SobolevSpace.toLp m q U =ᵐ[m.restrict Ω] fun x => Real.log (kernelHeat m q hk t f x)) ∧
      (SobolevSpace.toLp m q V =ᵐ[m.restrict Ω] fun x => Real.log (kernelHeat m q hk (T-t) g x)) ∧
      ∀ (w : SobolevSpace m q) (C : ℝ≥0),
        (∀ᵐ x ∂m, |SobolevSpace.toLp m q w x| ≤ C) →
        (∀ᵐ x ∂m, x ∉ Ω → SobolevSpace.toLp m q w x = 0) →
        HasDerivAt (fun s => ∫ x, SobolevSpace.toLp m q w x*
          (kernelHeat m q hk s f x*kernelHeat m q hk (T-s) g x) ∂m)
          (∫ x, kernelHeat m q hk t f x*kernelHeat m q hk (T-t) g x*
            localGamma m q (V-U) w x ∂m) t := by
  intro m q hk
  obtain ⟨u,v,hu,hv,hder⟩ := hX.kernelHeat_continuity_equation hn p hk f g A B hf hg ht htT
  obtain ⟨U,_dU,_Uf,_LU,_BU,_hdU,_hUf,_hUB,_hUr,hU⟩ :=
    hX.bounded_heat_log_regular hn p f A hf ht hΩ hpf
  obtain ⟨V,_dV,_Vf,_LV,_BV,_hdV,_hVf,_hVB,_hVr,hV⟩ :=
    hX.bounded_heat_log_regular hn p g B hg (sub_pos.mpr htT) hΩ hpg
  obtain ⟨a,b,ha,hab,hfr⟩ := hX.bounded_heat_positive_range hn p f A hf ht hΩ hpf
  obtain ⟨c,d,hc,hcd,hgr⟩ := hX.bounded_heat_positive_range hn p g B hg (sub_pos.mpr htT) hΩ hpg
  have hfr' : ∀ᵐ x ∂m.restrict Ω, SobolevSpace.toLp m q u x ∈ Icc a b := by
    filter_upwards [hfr,ae_restrict_of_ae hu,
      ae_restrict_of_ae (kernelHeat_represents_L2 m q hk ht f)] with x hx hy hz
    change kernelHeat m q hk t f x = SobolevSpace.toLp m q u x at hy
    change heatAt m q t f x ∈ Icc a b at hx
    rw [← hz,hy] at hx
    exact hx
  have hgr' : ∀ᵐ x ∂m.restrict Ω, SobolevSpace.toLp m q v x ∈ Icc c d := by
    filter_upwards [hgr,ae_restrict_of_ae hv,
      ae_restrict_of_ae (kernelHeat_represents_L2 m q hk (sub_pos.mpr htT) g)] with x hx hy hz
    change kernelHeat m q hk (T-t) g x = SobolevSpace.toLp m q v x at hy
    change heatAt m q (T-t) g x ∈ Icc c d at hx
    rw [← hz,hy] at hx
    exact hx
  have hUl : SobolevSpace.toLp m q U =ᵐ[m.restrict Ω]
      fun x => Real.log (SobolevSpace.toLp m q u x) := by
    filter_upwards [hU,ae_restrict_of_ae hu] with x hx hy
    exact hx.trans (congrArg Real.log hy)
  have hVl : SobolevSpace.toLp m q V =ᵐ[m.restrict Ω]
      fun x => Real.log (SobolevSpace.toLp m q v x) := by
    filter_upwards [hV,ae_restrict_of_ae hv] with x hx hy
    exact hx.trans (congrArg Real.log hy)
  refine ⟨U,V,hU,hV,?_⟩
  intro w C hw hwz
  have hUg : localGamma m q U w =ᵐ[m.restrict Ω]
      fun x => localGamma m q u w x/kernelHeat m q hk t f x := by
    filter_upwards [local_logarithm_gamma_of_value m q u U ha hab hfr' hUl w,
      ae_restrict_of_ae hu] with x hx hy
    exact hx.trans (by rw [hy])
  have hVg : localGamma m q V w =ᵐ[m.restrict Ω]
      fun x => localGamma m q v w x/kernelHeat m q hk (T-t) g x := by
    filter_upwards [local_logarithm_gamma_of_value m q v V hc hcd hgr' hVl w,
      ae_restrict_of_ae hv] with x hx hy
    exact hx.trans (by rw [hy])
  have he := local_logarithmic_difference_flux m q hΩ.measurableSet
    (kernelHeat m q hk t f) (kernelHeat m q hk (T-t) g) hpf hpg u v U V w 1 hUg hVg hwz
  have heq : (∫ x, kernelHeat m q hk t f x*localGamma m q v w x-
      kernelHeat m q hk (T-t) g x*localGamma m q u w x ∂m) =
      ∫ x, kernelHeat m q hk t f x*kernelHeat m q hk (T-t) g x*
        localGamma m q (V-U) w x ∂m := by
    apply integral_congr_ae
    simpa only [one_mul,one_smul] using he
  rw [← heq]
  exact hder w C hw

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
