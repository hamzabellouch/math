import OAI.Geometry.RCD.Transport.AmbientOptimalDualSaturation
import OAI.Geometry.RCD.Heat.HeatEnvelopeSegments
import OAI.Geometry.RCD.Heat.ContinuousKernelSaturation

namespace OAI

/-! # The actual heat envelope calibrates every ambient optimal coupling -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
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

theorem optimal_coupling_calibration (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (P : Measure (X × X)) (hP : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val) P) :
    ∃ A : ℝ, ∀ᵐ z ∂P, ∀ s ∈ Ioo (0:ℝ) 1, ∀ x : X,
      dist x z.1=s*dist z.1 z.2 → dist x z.2=(1-s)*dist z.1 z.2 →
      D.forward.potential (s/2) x=(D.backward.potential (1/2) a₀-D.backward.potential (1/2) z.1)-
        s*dist z.1 z.2^2-A := by
  obtain ⟨c,hc,hd,_⟩ := D.dual_limit a₀ b₀ hK hε1 hε0 hR hdS hdT
  obtain ⟨A,hA⟩ := D.forward_segment_values a₀ b₀ c hK hε0 hR hdS hd
  obtain ⟨Q,_,_,_,hl,hr,hs⟩ := continuous_kernel_saturation μ ν D.density D.density_pos
    D.density_row D.density_col (fun k => ε (D.index k)) (fun k => (hε (D.index k)).le)
    (D.slack a₀ b₀ c) hd (D.density_log_limit a₀ b₀ c hK hε1 hε0 hR hdS hdT hc)
  have hS : MeasurableSet S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hT : MeasurableSet T := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hdual (a : S) (b : T) (hb : b ∈ ν.support) :
      D.leftPotential a₀ a+D.rightPotential b₀ b+c ≤ dist (a : X) (b : X)^2 := by
    have hh := hd a b hb
    linarith
  have heq : ∀ᵐ z ∂(Q : Measure (S × T)), D.leftPotential a₀ z.1+D.rightPotential b₀ z.2+c=
      dist (z.1 : X) (z.2 : X)^2 := by
    filter_upwards [hs] with z hz
    change D.leftPotential a₀ z.1-dist (z.1 : X) (z.2 : X)^2+D.rightPotential b₀ z.2+c=0 at hz
    linarith
  obtain ⟨L,hL,hLl,hLr,hLs⟩ := ambient_optimal_dual_saturation hS hT μ ν Q hl hr
    (D.leftPotential a₀) (D.rightPotential b₀) c hdual heq P hP
  have hleft : ∀ᵐ z ∂L, z.1 ∈ μ.support := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hLl]
    exact μ.support_mem_ae
  have hright := coupling_snd_support (ν := ν) (π := L) hLr
  let inc : S × T → X × X := Prod.map Subtype.val Subtype.val
  have hi : MeasurableEmbedding inc :=
    (MeasurableEmbedding.subtype_coe hS).prodMap (MeasurableEmbedding.subtype_coe hT)
  refine ⟨A,?_⟩
  rw [← hL]
  apply hi.ae_map_iff.mpr
  filter_upwards [hleft,hright,hLs] with z hz hzb hzs
  have hzero : D.slack a₀ b₀ c z=0 := by
    change D.leftPotential a₀ z.1-dist (z.1 : X) (z.2 : X)^2+D.rightPotential b₀ z.2+c=0
    linarith
  exact hA z.1 hz z.2 hzb hzero

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
