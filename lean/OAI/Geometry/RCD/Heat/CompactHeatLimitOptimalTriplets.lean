import OAI.Geometry.RCD.Heat.CompactHeatJointGeodesic
import OAI.Geometry.RCD.Heat.CompactHeatJointLimit
import OAI.Geometry.RCD.Transport.CompactCouplingAmbientCost

namespace OAI

/-! # Every actual interior law is an interpolation of an optimal endpoint coupling -/

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

theorem interpolation_limit_optimal_triplets (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (t : Ioo (0:ℝ) 1) (i : ℕ → ℕ) (hi : StrictMono i) (Q₀ : ProbabilityMeasure X)
    (hweak : Tendsto (fun k => D.interpolationLaw (D.index (i k)) t) atTop (𝓝 Q₀)) :
    ∃ (P : ProbabilityMeasure (X × (S × T))) (j : ℕ → ℕ), StrictMono j ∧
      Tendsto (fun k => D.jointLaw (D.index (i (j k))) t) atTop (𝓝 P) ∧
      P.map Prod.fst=Q₀ ∧
      IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
        (((P.map Prod.snd).map (Prod.map Subtype.val Subtype.val)) : Measure (X × X)) ∧
      (∀ᵐ z ∂(P : Measure (X × (S × T))),
        dist z.1 (z.2.1:X)=(t:ℝ)*dist (z.2.1:X) (z.2.2:X) ∧
          dist z.1 (z.2.2:X)=(1-(t:ℝ))*dist (z.2.1:X) (z.2.2:X)) ∧
      (∀ᵐ x ∂(Q₀ : Measure X), dist x p ≤ 3*R) := by
  obtain ⟨P,j,hj,hP,hfirst,_⟩ := D.joint_limit hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT i t Q₀ hweak
  have hij : StrictMono (i ∘ j) := hi.comp hj
  obtain ⟨c,hdual,hgeo⟩ := D.joint_limit_geodesic a₀ b₀ hK hε1 hε0
    (zero_le_one.trans hR) hS hT t (i ∘ j) hij P hP
  obtain ⟨hl,hr⟩ := D.joint_limit_endpoint_marginals t (i ∘ j) P hP
  let E := P.map Prod.snd
  have heq : ∀ᵐ z ∂(E : Measure (S × T)),
      D.leftPotential a₀ z.1+D.rightPotential b₀ z.2+c=dist (z.1:X) (z.2:X)^2 := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    filter_upwards [hgeo] with z hz
    have hh := hz.2.2
    dsimp only [slack,ContinuousMap.coe_mk] at hh
    linarith only [hh]
  let cost : C(S × T,ℝ) := ⟨fun z => dist (z.1:X) (z.2:X)^2,by fun_prop⟩
  have hmin := compact_dual_cost_minimizer μ ν (E : Measure (S × T)) hl hr
    (D.leftPotential a₀) (D.rightPotential b₀) cost c
    (fun a b hb => by
      have hh := hdual a b hb
      change D.leftPotential a₀ a + D.rightPotential b₀ b + c ≤ dist (a:X) (b:X)^2
      dsimp only [slack,ContinuousMap.coe_mk] at hh
      linarith only [hh]) heq
  have hopt := compact_coupling_ambient_optimal
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace S)).isClosed.measurableSet
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace T)).isClosed.measurableSet
    μ ν E hl hr hmin
  have hbounded := D.joint_limit_bounded a₀ b₀ hK hε1 hε0
    (zero_le_one.trans hR) hS hT t (i ∘ j) hij P hP
  rw [hfirst] at hbounded
  exact ⟨P,j,hj,hP,hfirst,hopt,hgeo.mono (fun _ hz => ⟨hz.1,hz.2.1⟩),hbounded⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
