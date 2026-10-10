import OAI.Geometry.RCD.Transport.LengthComponentDyadic
import OAI.Geometry.RCD.Transport.CompressedSubplanNode
import OAI.Geometry.RCD.Transport.MaximalTreeScalarChord
import OAI.Geometry.RCD.Coordinates.RenyiChordNormalization

namespace OAI

/-! # The exact scalar chord at the actual length scale of each component -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.component_scalar_chord
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    {m : ℕ} (hm : RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m)
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ : Measure C(Time,X)) (heκ : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (hκ0 : κ univ≠0) {D : ℝ} (hD0 : 0≤D) (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D) :
    ∀ t∈dyadicGrid m,
      reducedChord K (N+1) D
        (renyiIntegral (hausdorff n X) (κ.map (fun γ => γ 0)) N)
        (renyiIntegral (hausdorff n X) (κ.map (fun γ => γ 1)) N) t ≤
          renyiIntegral (hausdorff n X) (κ.map (fun γ => γ t)) N := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hN1 : 1<N := by linarith
  have hq0 : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN1)
  have hq1 : 1-1/N<1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  have hκ : κ≤π := by rw [heκ]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hκtop : κ univ≠∞ := measure_ne_top κ univ
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,_⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  obtain ⟨b,hb0,hb1,hbD⟩ := hX.compressed_subplan_node K n hn a π hg hp hC hc κ hκ hκ0 hD0 hD
  have hpb : IsOptimalCoupling b.left b.right (πn.map (fun γ => (γ 0,γ 1))) := by
    rw [hb0,hb1,←heval,←heval]; exact hpn
  have hmn := hX.length_component_dyadic_maximal K n hn hq0 hq1 hC m a π inferInstance
    hg hp hc hm S hS κ heκ hκ0
  have hcn := normalized_subplan_compression π κ hκ hc
  have hcf : (κ univ)⁻¹*C≠∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hκ0) hC
  intro t ht
  have hh := hX.maximal_tree_scalar_chord K n hn hK hN hcf m b πn hπn hgn hpb hcn hmn t ht
  rw [hbD,heval,heval,heval] at hh
  exact renyiIntegral_normalized_chord μ _ _ _ hκ0 hκtop hN1 hh

end RegularPointCoordinates

end

end OAI
