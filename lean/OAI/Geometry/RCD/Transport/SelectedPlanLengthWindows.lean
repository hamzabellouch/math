import OAI.Geometry.RCD.Transport.LengthComponentCompression
import OAI.Geometry.RCD.Transport.ReducedInterpolation

namespace OAI

/-! # The selected interpolation has uniform bounds on each length window -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_reduced_plan_with_length_windows
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X) :
    ∃ π : ProbabilityMeasure C(Time,X),
      (∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ) ∧
      IsOptimalCoupling a.left a.right ((π : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) ∧
      (∀ t, ReducedRenyiChordBound (hausdorff n X) K N (π : Measure C(Time,X)) t) ∧
      ∀ D : ℝ, 0≤D → ∀ t : Time,
        (((π : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<D}).map (fun γ => γ t))≤
          compressionBudget K n D a.capacity • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  have hN1 : 1<N := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hq0 : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN1)
  have hq1 : 1-1/N<1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  obtain ⟨π,hπ,hg,hp,hc,hm,_⟩ := hX.exists_compressed_renyi_chord K n hn hK hN a
  let := hπ
  have hcf := compressionBudget_ne_top K n a.distance a.capacity_finite
  refine ⟨⟨π,hπ⟩,hg,hp,hX.compressed_reduced_interpolation K n hn hK hN a π hg hp hcf hc hm,?_⟩
  intro D hD
  apply hX.length_component_compression K n hn hq0 hq1 a π hg hp hcf hc hm
    measurableSet_Iio _ rfl hD
  exact (ae_restrict_mem (by
    exact measurableSet_Iio.preimage ((measurable_path_eval 0).dist (measurable_path_eval 1)))).mono
    (fun _ h => h.le)

end RegularPointCoordinates

end

end OAI
