import OAI.Geometry.RCD.Heat.FixedHeatEnvelope
import OAI.Geometry.RCD.Heat.OptimalHeatPlanCalibration

namespace OAI

/-! # Calibration with the fixed envelope gauge

The same scalar normalization is retained by the envelope, coupling and
all-time geodesic identities, so their contact potentials can be identified.
-/

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

theorem forward_segment_values_fixed_gauge (a₀ : S) (b₀ : T) (c : ℝ) (hK : K ≤ 0)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R)
    (hdual : ∀ a b, b ∈ ν.support → D.slack a₀ b₀ c (a,b) ≤ 0) :
    ∀ a ∈ μ.support, ∀ b ∈ ν.support,
      D.slack a₀ b₀ c (a,b)=0 → ∀ s ∈ Ioo (0:ℝ) 1, ∀ x : X,
      dist x (a : X)=s*dist (a : X) (b : X) →
      dist x (b : X)=(1-s)*dist (a : X) (b : X) →
      D.forward.potential (s/2) x=D.leftPotential a₀ a-s*dist (a : X) (b : X)^2-D.forwardGauge a₀ hK hε0 hR hdS := by
  have hE := D.forward_gauge_envelope a₀ hK hε0 hR hdS
  intro a ha b hb hz s hs x hxa hxb
  have hhalf : s/2 ∈ Ioo (0:ℝ) 1 := ⟨half_pos hs.1,by linarith [hs.2]⟩
  obtain ⟨m,_,hm,hval⟩ := hE (s/2) hhalf x
  have he : 2*(s/2)=s := by ring
  simp only [he] at hm hval
  have hbound (u : S) : D.leftPotential a₀ u+(D.rightPotential b₀ b+c) ≤ dist (u : X) (b : X)^2 := by
    have hh := hdual u b hb
    change D.leftPotential a₀ u-dist (u : X) (b : X)^2+D.rightPotential b₀ b+c ≤ 0 at hh
    linarith
  have heq : D.leftPotential a₀ a+(D.rightPotential b₀ b+c)=dist (a : X) (b : X)^2 := by
    change D.leftPotential a₀ a-dist (a : X) (b : X)^2+D.rightPotential b₀ b+c=0 at hz
    linarith
  have hv := dual_segment_envelope (D.leftPotential a₀) a m b x
    (D.rightPotential b₀ b+c) s hs.1 hs.2.le hbound heq hxa hxb (hm a ha)
  rw [hv] at hval
  exact hval

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

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

theorem optimal_coupling_fixed_gauge_calibration (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (P : Measure (X × X)) (hP : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val) P) :
    ∀ᵐ z ∂P, ∀ s ∈ Ioo (0:ℝ) 1, ∀ x : X,
      dist x z.1=s*dist z.1 z.2 → dist x z.2=(1-s)*dist z.1 z.2 →
      D.forward.potential (s/2) x=(D.backward.potential (1/2) a₀-D.backward.potential (1/2) z.1)-
        s*dist z.1 z.2^2-D.forwardGauge a₀ hK hε0 hR hdS := by
  obtain ⟨c,hc,hd,_⟩ := D.dual_limit a₀ b₀ hK hε1 hε0 hR hdS hdT
  have hA := D.forward_segment_values_fixed_gauge a₀ b₀ c hK hε0 hR hdS hd
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
  rw [← hL]
  apply hi.ae_map_iff.mpr
  filter_upwards [hleft,hright,hLs] with z hz hzb hzs
  have hzero : D.slack a₀ b₀ c z=0 := by
    change D.leftPotential a₀ z.1-dist (z.1 : X) (z.2 : X)^2+D.rightPotential b₀ z.2+c=0
    linarith
  exact hA z.1 hz z.2 hzb hzero

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

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
attribute [local instance] pathBorel pathBorelSpace

theorem optimal_plan_fixed_gauge_calibration (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (π : Measure C(Time,X)) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1)))) :
    ∀ᵐ γ ∂π, ∀ s : Time, 0 < (s : ℝ) → (s : ℝ) < 1 →
      D.forward.potential ((s : ℝ)/2) (γ s)=
        (D.backward.potential (1/2) a₀-D.backward.potential (1/2) (γ 0))-
          (s : ℝ)*dist (γ 0) (γ 1)^2-D.forwardGauge a₀ hK hε0 hR hdS := by
  have hA := D.optimal_coupling_fixed_gauge_calibration a₀ b₀ hK hε1 hε0 hR hdS hdT
    (π.map (fun γ => (γ 0,γ 1))) hopt
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hh := ae_of_ae_map hm.aemeasurable hA
  filter_upwards [hgeo,hh] with γ hγ hcal
  intro s hs hs1
  have h0 : dist (γ s) (γ 0)=(s : ℝ)*dist (γ 0) (γ 1) := by
    simpa [abs_of_nonneg s.property.1] using hγ s 0
  have h1 : dist (γ s) (γ 1)=(1-(s : ℝ))*dist (γ 0) (γ 1) := by
    simpa [abs_of_nonpos (sub_nonpos.mpr s.property.2),neg_sub] using hγ s 1
  exact hcal s ⟨hs,hs1⟩ (γ s) h0 h1

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end
end
end

end OAI
