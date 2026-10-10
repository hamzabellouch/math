import OAI.Geometry.RCD.Heat.KernelHeatLogarithmicEquation
import OAI.Geometry.RCD.Heat.HeatLiYauParameter

namespace OAI

/-! # Li--Yau controls the actual local logarithmic weak source -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_logarithmic_liYau (hK : K ≤ 0) (α : ℝ) (hα : 1 < α)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t)
    {Ω : Set X} (hΩ : IsCompact Ω)
    (hpos : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic hk t f x) :
    ∃ (u v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
      (kernelHeat (hausdorff n X) hX.quadratic hk t f =ᵐ[hausdorff n X]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u) ∧
      IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
        fun x => Real.log (kernelHeat (hausdorff n X) hX.quadratic hk t f x)) ∧
      (∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        localGamma (hausdorff n X) hX.quadratic v w =ᵐ[(hausdorff n X).restrict Ω]
          fun x => localGamma (hausdorff n X) hX.quadratic u w x /
            kernelHeat (hausdorff n X) hX.quadratic hk t f x) ∧
      ∀ᵐ x ∂(hausdorff n X).restrict Ω,
        -(((n:ℝ)*α^2/2)*(|K|/(α-1)+1/t)) ≤
          α*q x+(α-1)*localGamma (hausdorff n X) hX.quadratic v v x := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let H := kernelHeat m Q hk t f
  obtain ⟨u,v,q,hu,hq,hv,hder,hchain⟩ :=
    hX.kernelHeat_logarithmic_equation hn p hk f A hf ht hΩ hpos
  have hre := kernelHeat_represents_L2 m Q hk ht f
  have hue : u = heatSobolev m Q t ht f := by
    apply Subtype.ext
    exact Lp.ext (hu.symm.trans hre)
  refine ⟨u,v,q,hu,hq,hv,hchain,?_⟩
  filter_upwards [hder,hchain u,hchain v,ae_restrict_of_ae (localGamma_comm m Q u v),
    ae_restrict_of_ae hre,ae_restrict_of_ae (kernelHeatGeneratorSource_represents m Q hk ht f),
    ae_restrict_of_ae (hX.heat_liYau_parameter hn p hK α hα f hf0 A hf ht),
    ae_restrict_of_ae (Lp.coeFn_neg (heatGeneratorAt m Q t f)),
    ae_restrict_mem hΩ.measurableSet] with x hd hcu hcv hsym hr hs hly hneg hx
  have hp : 0 < H x := hpos x hx
  have he := hd.unique (kernelHeat_log_hasDerivAt m Q hk f ht x hp.ne')
  have hgram : localGamma m Q v v x = localGamma m Q u u x/(H x)^2 := by
    rw [hcv,hsym,hcu,div_div,pow_two]
  rw [← hue,← hr] at hly
  rw [hgram] at he ⊢
  change q x+localGamma m Q u u x/(H x)^2 =
    kernelHeatGeneratorSource m Q hk t f x/H x at he
  rw [hs] at he
  have hmul := div_le_div_of_nonneg_right hly (sq_nonneg (H x))
  have hsq : (α*H x*((-heatGeneratorAt m Q t f : Lp ℝ 2 m) : X → ℝ) x+
      (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/t))*(H x)^2)/(H x)^2 =
      α*(((-heatGeneratorAt m Q t f : Lp ℝ 2 m) : X → ℝ) x/H x)+
        (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/t)) := by field_simp
  rw [hsq,hneg] at hmul
  rw [← he] at hmul
  linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
