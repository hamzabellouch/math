import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Nonnegative initial data for positive compact heat factors -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_nonnegative_L2 {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x|≤C)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S,ℝ)) (hF : ∀ a, 0≤F a) :
    ∃ (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0), 0≤f ∧
      (∀ᵐ x ∂hausdorff n X, |f x|≤A) ∧
      ∀ (t : ℝ) (ht : 0<t) (x : X), hX.compactHeatFactor hn p ν F t ht x =
        kernelHeat (hausdorff n X) hX.quadratic
          (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x := by
  let m := hausdorff n X
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  let f₀ := fun x => ρ x*compactFactorExtension F x
  have hm : MemLp f₀ 2 m := compact_weighted_density_memLp hS F m hρ hC
  let f := hm.toLp f₀
  have hf : f =ᵐ[m] f₀ := hm.coeFn_toLp
  have hf0 : 0≤f := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hf] with x hx
    rw [hx]
    apply mul_nonneg (hρ0 x)
    by_cases hs : x∈S
    · exact (compactFactorExtension_coe F ⟨x,hs⟩) ▸ hF ⟨x,hs⟩
    · rw [compactFactorExtension_off F hs]
  obtain ⟨A,hA⟩ := compact_weighted_density_bounded hS F m hC
  refine ⟨f,A,hf0,?_,?_⟩
  · filter_upwards [hf,hA] with x hx hax
    exact hx ▸ hax
  · intro t ht x
    change (∫ a, hX.canonicalHeatKernel hn p t x a*F a ∂ν) = _
    calc
      _ = ∫ y, hX.canonicalHeatKernel hn p t x y*f₀ y ∂m :=
        compact_weighted_density_integral hS.isClosed.measurableSet m ν ρ hρ hρ0 hν F _
      _ = ∫ y, hX.canonicalHeatKernel hn p t x y*f y ∂m := by
        apply integral_congr_ae
        filter_upwards [hf] with y hy
        rw [hy]
      _ = _ := (kernelHeat_eq_integral m hX.quadratic
        (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) ht f x).symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
