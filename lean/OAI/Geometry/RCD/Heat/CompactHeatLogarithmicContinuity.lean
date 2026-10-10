import OAI.Geometry.RCD.Heat.KernelHeatLogarithmicContinuity
import OAI.Geometry.RCD.Heat.CompactHeatVelocityPotential
import OAI.Geometry.RCD.Heat.CompactHeatInterpolationMean

namespace OAI

/-! # The physical-time continuity equation of the actual interpolation -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationMean_logarithmic_continuity
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (k : ℕ) (t : Ioo (0:ℝ) 1) {Ω : Set X} (hΩ : IsCompact Ω) :
    let m := hausdorff n X
    let q := hX.quadratic
    ∃ θ : SobolevSpace m q,
      (SobolevSpace.toLp m q θ =ᵐ[m.restrict Ω] D.velocityPotential k t) ∧
      ∀ (w : SobolevSpace m q) (C : ℝ≥0),
        (∀ᵐ x ∂m, |SobolevSpace.toLp m q w x| ≤ C) →
        (∀ᵐ x ∂m, x ∉ Ω → SobolevSpace.toLp m q w x = 0) →
        HasDerivAt (D.interpolationMean (SobolevSpace.toLp m q w) k)
          (∫ x, D.interpolationDensity k t x*localGamma m q θ w x ∂m) t := by
  intro m q
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let c := ε k/4
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hs : 0 < c*(t:ℝ) := mul_pos hc t.property.1
  have ht : c*(t:ℝ) < c := mul_lt_of_lt_one_right hc t.property.2
  obtain ⟨f,⟨A,hf⟩,hef⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨g,⟨B,hg⟩,heg⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  have hback : c-c*(t:ℝ) = c*(1-t) := by ring
  have hfrontrep (x : X) : kernelHeat m q hk (c*t) f x =
      hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t)
        (mul_pos (div_pos (hε k) (by norm_num)) t.property.1) x := (hef _ hs x).symm
  have hbackrep (x : X) : kernelHeat m q hk (c-c*t) g x =
      hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t))
        (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)) x := by
    simpa only [hback,c] using (heg _ (sub_pos.mpr ht) x).symm
  have hpf : ∀ x ∈ Ω, 0 < kernelHeat m q hk (c*t) f x := by
    intro x _
    rw [← hef _ hs x]
    exact hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x
  have hpg : ∀ x ∈ Ω, 0 < kernelHeat m q hk (c-c*t) g x := by
    intro x _
    rw [← heg _ (sub_pos.mpr ht) x]
    simpa only [hback] using hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k)
      (c*(1-t)) (mul_pos hc (sub_pos.mpr t.property.2)) x
  obtain ⟨U,V,hU,hV,hder⟩ := hX.kernelHeat_logarithmic_continuity hn p f g A B hf hg hs ht hΩ hpf hpg
  let θ := c • (V-U)
  have hθ : SobolevSpace.toLp m q θ =ᵐ[m.restrict Ω] D.velocityPotential k t := by
    filter_upwards [hU,hV,ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp m q V) (SobolevSpace.toLp m q U)),
      ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp m q (V-U)))] with x hu hv hsub hmul
    change SobolevSpace.toLp m q θ x = c*SobolevSpace.toLp m q (V-U) x at hmul
    simp only [Pi.sub_apply] at hsub
    rw [hmul]
    simp only [map_sub]
    rw [hsub,hu,hv,hfrontrep,hbackrep]
    rfl
  refine ⟨θ,hθ,?_⟩
  intro w C hw hwz
  have hd := (hder w C hw hwz).scomp (t:ℝ) ((hasDerivAt_id (t:ℝ)).const_mul c)
  have hcoeff : c*(∫ x, kernelHeat m q hk (c*t) f x*kernelHeat m q hk (c-c*t) g x*
      localGamma m q (V-U) w x ∂m) = ∫ x, D.interpolationDensity k t x*localGamma m q θ w x ∂m := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [localGamma_smul_left m q c (V-U) w] with x hx
    change c*(_*_*_) = _*localGamma m q (c • (V-U)) w x
    rw [hx,hfrontrep,hbackrep]
    dsimp only [interpolationDensity]
    ring
  have hd' : HasDerivAt (fun s => ∫ x, SobolevSpace.toLp m q w x*
      (kernelHeat m q hk (c*s) f x*kernelHeat m q hk (c-c*s) g x) ∂m)
      (∫ x, D.interpolationDensity k t x*localGamma m q θ w x ∂m) t := by
    change HasDerivAt (fun s => ∫ x, SobolevSpace.toLp m q w x*
      (kernelHeat m q hk (c*s) f x*kernelHeat m q hk (c-c*s) g x) ∂m)
      ((c*1) • (∫ x, kernelHeat m q hk (c*t) f x*kernelHeat m q hk (c-c*t) g x*
        localGamma m q (V-U) w x ∂m)) t at hd
    simpa only [mul_one,smul_eq_mul,hcoeff] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with s hs'
  have hsf : 0 < c*s := mul_pos hc hs'.1
  have hsg : 0 < c-c*s := by nlinarith [hs'.2]
  have hbs : c-c*s = c*(1-s) := by ring
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change SobolevSpace.toLp m q w x *
      ((∫ y, hX.canonicalHeatKernel hn p (c*s) x y*D.left k y ∂μ)*
        (∫ y, hX.canonicalHeatKernel hn p (c*(1-s)) x y*D.right k y ∂ν)) =
      SobolevSpace.toLp m q w x*(kernelHeat m q hk (c*s) f x*kernelHeat m q hk (c-c*s) g x)
    rw [← hef _ hsf x,← heg _ hsg x]
    simp only [hbs,compactHeatFactor,compactKernelFactor,compactHeatFactorKernel]
    rfl

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
