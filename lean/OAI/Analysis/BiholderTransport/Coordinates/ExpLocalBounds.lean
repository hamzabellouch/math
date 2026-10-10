import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactLocalPositiveBounds
import OAI.Analysis.BiholderTransport.Coordinates.ExpVertical
import OAI.Analysis.BiholderTransport.LinearAlgebra.OperatorBounds

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpLocalBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventually_exp_differential_bounds {c : TangentBundle 𝓘(ℝ,Model n) M}
    (hc : c.2∈injectivityDomain c.1) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 c,
      ∀ v : TangentSpace 𝓘(ℝ,Model n) z.1,
      l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖≤u*‖v‖ := by
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let U := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let V := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  obtain ⟨l,u,hl,hu,hlu⟩ := eventually_injective_operator_bounds
    (coordinateEndpointVertical_continuousAt c) (coordinateEndpointVertical_injective hc)
  obtain ⟨CU,hCU,hUb⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  obtain ⟨DU,hDU,hUib⟩ := eventually_norm_symmL_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  obtain ⟨CV,hCV,hVb⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  obtain ⟨DV,hDV,hVib⟩ := eventually_norm_symmL_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  have hproj : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
    (Bundle.contMDiff_proj (n := ∞) (IB := 𝓘(ℝ,Model n)) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).continuous
  have hE := (contMDiff_riemannianExp (n := n) (M := M)).continuous.continuousAt (x := c)
  have hsource := extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  have htarget := hE.eventually (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) (riemannianExp c.1 c.2))
  refine ⟨l/(DU*CV),DV*u*CU,div_pos hl (mul_pos hDU hCV),
    mul_pos (mul_pos hDV hu) hCU,?_⟩
  filter_upwards [hlu,hsource,htarget,hproj.continuousAt.eventually hUb,
    hproj.continuousAt.eventually hUib,hE.eventually hVb,hE.eventually hVib]
    with z hz hzs hzt hzU hzUi hzV hzVi
  have hzUs : z.1∈U.baseSet := by
    simpa only [U,TangentBundle.trivializationAt_baseSet,extChartAt_source]
      using (tangent_chart_source_iff c z).mp hzs
  have hzVs : riemannianExp z.1 z.2∈V.baseSet := by
    dsimp only [V]
    rw [TangentBundle.trivializationAt_baseSet]
    rw [extChartAt_source] at hzt
    exact hzt
  exact operator_bounds_through_charts (U.continuousLinearMapAt ℝ z.1) (U.symmL ℝ z.1)
    (V.continuousLinearMapAt ℝ (riemannianExp z.1 z.2)) (V.symmL ℝ (riemannianExp z.1 z.2))
    (coordinateEndpointVertical c z)
    (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2)
    (U.symmL_continuousLinearMapAt hzUs) (V.symmL_continuousLinearMapAt hzVs)
    (coordinateEndpointVertical_apply c z hzs hzt)
    hl hu hCU hDU hCV hDV hzU.le hzUi.le hzV.le hzVi.le hz

end ExpLocalBounds
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpCompactBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma compact_exp_differential_bounds {K : Set (TangentBundle 𝓘(ℝ,Model n) M)}
    (hK : IsCompact K) (hI : ∀ z∈K, z.2∈injectivityDomain z.1) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ z∈K, ∀ v : TangentSpace 𝓘(ℝ,Model n) z.1,
      l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖≤u*‖v‖ := by
  apply compact_local_positive_bounds hK
  · intro r R b B hr hrR hbB z hz v
    exact ⟨(mul_le_mul_of_nonneg_right hrR (norm_nonneg v)).trans (hz v).1,
      (hz v).2.trans (mul_le_mul_of_nonneg_right hbB (norm_nonneg v))⟩
  · exact fun z hz => eventually_exp_differential_bounds (hI z hz)

end ExpCompactBounds
end WeakMTWTransport

end

end

end

end OAI
